# Summation and dot-product reference

Evaluation schedules, mixed error bounds, and range certificates for sums
and dot products. Start with [Using FP](Using.md) for the theorem map and the
[IEEE dot-product example](../examples/consumer/Examples/IEEEDot.lean) for a
complete application. [Compensated arithmetic](Compensated.md) has its own reference.

## IEEE-facing executable reductions

The completion target is the formal IEEE specification. Further equivalence to
Lean's native logical model is optional; the existing native theorems remain available.

`FP.IEEE.Software` now provides `sumTree?`, `sequentialSum?`, `pairwiseSum?`,
and `dot?` over exact rational inputs. Their `_cast` theorems prove equivalence
to the IEEE finite-value specification, including propagation of overflow.
The proof modules for these reductions do not depend on `FP.Native`.

`wordSumTree?`, `wordSequentialSum?`, `wordPairwiseSum?`, and `wordDot?` start
from actual interchange words, e.g. `wordDot? fp32 a b n`. Their refinement
hypotheses require only the used inputs to decode to finite real values.
Outputs are `Option ℚ`: these interfaces do not yet return IEEE result encodings
or flags, and `none` can also arise from a nonfinite input.

The `_mixed_of_certificate` theorems supply a rational result, its certified
interval enclosure, and the existing mixed bound. For sums this is
`growth u height * mass + ε * roundWeight`; for dot products the componentwise
perturbation is `growth u (2*n)` with residual `ε*(2+u)*geomWeight u n`.
Here `u` is the format's unit roundoff and `ε = minSubnormal/2`.
They allow gradual underflow. The rational `sequentialSum?_backward`,
`pairwiseSum?_backward`, and `dot?_backward` theorems retain the stronger normal-range
conditions for purely relative backward stability. The dot certificate also has
`dot?_mixed_gamma_of_certificate` when `2*n*u < 1`.

## Total scheduled reductions and accumulated flags

`Software.sequentialSum fp32 mode a n`, `pairwiseSum`, `sumTree`, and `dot`
now operate on interchange words and return `Result I.Word`. Both formats and
all five modes are supported. Exceptional results remain actual NaNs or
infinities, computation continues, and operation flags accumulate through
`Result.bind`.

`sumTree_spec` and `dot_spec` prove evaluation relations built from the independent
arithmetic contracts. `sumTree_flags_iff` and `dot_flags_iff` prove that each final
flag is set exactly when an executed operation raised it. `sumEvents` and
`dotEvents` expose those operation-local flag sets in evaluation order.

These APIs execute the specified arithmetic schedules; they do not implement
the optional IEEE Clause 9 reduction operations. Empty schedules return +0 with
no flags. A singleton sum copies its input, even a signaling NaN, without an
arithmetic operation. A dot product starts at +0 and performs separate
multiplication and addition for every term. Input leaves outside the schedule
are not inspected.

For nearest-even, `sumTree_projection_of_some` and `dot_projection_of_some`
prove that a successful old finite evaluation has the same decoded total result.
The total `_mixed_of_certificate` theorems give a decoded real result, certified
enclosure, and the existing mixed bounds, allowing gradual underflow. The sum
bounds retain the sequential or pairwise schedule dependence; the dot bound
retains its componentwise perturbations and additive underflow residual.
`dot_mixed_gamma_of_certificate` gives the gamma specialization.

`sequentialSum_backward`, `pairwiseSum_backward`, and `dot_backward` now apply
to total result words under the original stronger `Safe` trace and size
conditions. These numerical bounds currently cover nearest-even; the all-mode
evaluation and flag theorems do not require those numerical qualifications.

## Mixed errors and certified ranges

`FP.MixedError u ε z zhat` means

```
|zhat - z| ≤ u * |z| + ε.
```

The library proves the equivalent decomposition
`zhat = z * (1 + δ) + ρ`, with `|δ| ≤ u` and `|ρ| ≤ ε`, for nonnegative
parameters. It supplies addition and multiplication composition rules, an
error-recurrence theorem, and the denominator-free geometric sum
`geomWeight u k = Σⱼ<k (1+u)^j`. These work at `u = 0` and without a
smallness assumption on the operation count. The IEEE instantiation uses
`ε = minSubnormal / 2` and the previously proved rounding-error bound.

### Sequential and pairwise summation

The real specification, native evaluator, and checker share a `ReductionTree`
with zero, indexed input, and addition nodes. Empty sums return zero and
singletons return their input without an addition. Sequential summation then
adds from left to right. Pairwise summation splits contiguous inputs into
`n/2` and `n-n/2` terms, preserving their order without zero padding.
Both schedules contain exactly `n-1` additions for nonempty inputs.

For `A = Σᵢ<n |xᵢ|`, the proved bound is

```
|computedSum - Σᵢ<n xᵢ| ≤ growth u h * A + ε * W.
```

| Schedule | Height `h` | Absolute-error weight `W` |
| --- | --- | --- |
| Sequential | `n-1` | `geomWeight u (n-1)` |
| Pairwise | `Nat.clog 2 n` | `ReductionTree.roundWeight u (pairwiseTree 0 n)` |

Subtraction in these counts is natural-number subtraction. The pairwise
weight also satisfies `W ≤ (n-1)*(1+u)^(h-1)`, including empty and singleton
inputs. In general `W` is zero at leaves and obeys
`W(add l r) = 1 + (1+u)*(W(l)+W(r))`.

Gamma corollaries replace `growth u h` by `gamma u h` when `h*u < 1`.
In the pure relative model, the library also proves componentwise backward
stability for both schedules. These compare worst-case bounds; they do not
assert that pairwise summation is more accurate on every individual input.

The executable functions are:

| Format | Sequential | Pairwise |
| --- | --- | --- |
| fp32 | `FP.Native.float32SequentialSum` | `FP.Native.float32PairwiseSum` |
| fp64 | `FP.Native.floatSequentialSum` | `FP.Native.floatPairwiseSum` |

They accept `a : ℕ → Float32` or `a : ℕ → Float` and a length `n`.
The specification counterparts are `Format.sequentialSum?` and
`Format.pairwiseSum?`. Native equivalence theorems use the function names
with the suffix `_equiv`.

### Dot products through underflow

`MixedBackwardStable β B x y n s` asserts

```
s = Σᵢ<n x'ᵢ*yᵢ + ρ
|x'ᵢ - xᵢ| ≤ β*|xᵢ|
|ρ| ≤ B.
```

With `B = 0` this is equivalent to the existing `BackwardStable` predicate.
For the existing zero-started, multiply-then-add dot algorithm, the new bounds
are

```
β = growth u (2*n)
B = dotResidual u ε n = ε*(2+u)*geomWeight u n
|s - Σᵢ<n xᵢ*yᵢ| ≤ β*Σᵢ<n |xᵢ*yᵢ| + B.
```

These results allow underflow, assuming nonoverflow. Their gamma versions
require `2*n*u < 1`. The previous purely relative theorems and their stronger
`SafeDot` hypotheses remain available.

### Using the checker

`FP.Range.Interval` has exact rational endpoints `lo` and `hi`.
`Interval.Contains x` means the real value `x` belongs to that closed interval.
`Params.ofFormat F` computes rational values of the format's unit roundoff,
half least subnormal, and overflow threshold; their equality to the real
specification constants is proved.

`checkSum` traverses a reduction tree. `checkDot` follows the existing dot
algorithm, checking both each product and each addition. Addition uses endpoint
sums; multiplication uses the extrema of all four endpoint products. Before
each rounding, the checker requires `max |lo| |hi| < overflowThreshold` and
then expands the interval by `u*max |lo| |hi| + ε`.

Success returns an output interval and proves all intermediate nonoverflow
conditions. `none` means that the supplied intervals did not certify the
computation, **not** that the actual computation necessarily overflows.
Malformed intervals are rejected when used as inputs. The checker is
conservative and does not track correlations between inputs.

For example, this certificate is proved by kernel reduction:

```lean
have hc :
    (FP.Range.checkSum (.ofFormat FP.IEEE.binary32)
      (fun _ => ⟨-1, 1⟩) (FP.pairwiseTree 0 5)).isSome = true := by
  decide +kernel
```

Given `hx : ∀ i < 5, FP.Native.float32Value (a i) = some (x i)` and
`hb : ∀ i < 5, (⟨-1,1⟩ : FP.Range.Interval).Contains (x i)`, apply

```lean
FP.Native.float32PairwiseSum_mixed_of_certificate
  a x (fun _ => ⟨-1, 1⟩) 5 hx hb hc
```

The conclusion supplies a finite native result and the mixed forward bound;
there is no caller-supplied operation trace. Replace `float32` with `float` for
fp64, or `Pairwise` with `Sequential` for sequential summation. The suffix
`_mixed_gamma_of_certificate` selects the gamma bound.

Dot-product entry points are `float32Dot_mixed_of_certificate` and
`floatDot_mixed_of_certificate`, with `_mixed_gamma_of_certificate` and
`_mixed_forward_of_certificate` variants. They accept input intervals for
both vectors. Separate `checkSum_sound` and `checkDot_sound` theorems expose
the output enclosure as well as the trace proof.

`decide +kernel` asks Lean's kernel to verify a closed computation; it is not
`native_decide` and introduces no native evaluation oracle. The executable
checker uses rational arithmetic throughout. Its soundness proofs and the
real-value error analysis are noncomputable proof-side declarations.

`FP/MixedBoundaries.lean` contains complete examples for both formats, including
five-term certified native sums, signed cancellation, subnormal summation,
and certified mixed backward explanations of `minSubnormal * (1/2) = 0`.
The earlier proof that this underflow result is not purely relatively backward
stable remains valid.
