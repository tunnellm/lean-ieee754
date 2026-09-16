# Compensated arithmetic reference

TwoSum, TwoProduct, compensated summation, and compensated dot products.
These results keep their finite-execution and underflow qualifications.
For ordinary sums and dot products, see [Reductions](Reductions.md).
For a complete theorem application, see the
[compensated-sum example](../examples/consumer/Examples/CompensatedSum.lean).

## Classical TwoSum and compensated summation

`Software.twoSum I a b` executes the classical six-operation nearest-even schedule:
`s=a+b`, `bv=s-a`, `av=s-bv`, `br=b-bv`, `ar=a-av`, `e=ar+br`, with each
operation rounded in `I`. `twoSum_spec` proves total refinement to the independent
`Spec.TwoSum` schedule, including exceptional operands and the union of all six
flag sets. This is the classical TwoSum algorithm, not a rational reimplementation
of its output residual.

`twoSum_exact_of_finite_stages` proves the general exact-decomposition theorem:
for finite inputs `x,y`, if the initial rounded sum `s` and virtual second addend
`bv` are finite, the actual output words decode to `s` and **`x+y-s` exactly**.
There is no operand-ordering, normal-range, reconstruction-exactness, or
certificate-success assumption. The theorem applies to every valid binary
interchange format, including fp32 and fp64, with gradual underflow.

`twoSum_reconstruction_values_of_finite_stages` proves all four reconstruction
values finite and exact. `_reconstruction_flags_of_finite_stages` proves their
flags empty, so `twoSum_flags_of_finite_stages` reduces the total flags to the
union of the initial addition and `bv` subtraction flags. Both may be inexact.
The algorithm and its six-operation IEEE specification are unchanged.

`certifiedTwoSum?_of_finite_stages` derives success of the existing executable
certificate. `_success_iff_finite_stages` characterizes success exactly by the
finiteness of the inputs, `s`, and `bv`; its reconstruction checks are therefore
redundant under those conditions. Earlier `_complete`, `_of_exact_sum`,
`_of_absorbed`, `_of_cancellation`, and `_of_two_reconstructions` interfaces remain
available.

`twoSum_exact_of_range` provides a real-decoding version with explicit conditions:

```text
abs(x+y) < overflowThreshold
abs(roundFinite(x+y)-x) < overflowThreshold
```

**Necessary qualification:** finiteness of the initial sum alone does not suffice.
For fp32, inputs `0xf3c00000` and `0x7f7fffff` produce finite high word
`0x7f7ffffe`, but `bv` overflows and the error word is NaN. The analogous fp64
inputs are `0xfca8000000000000` and `0x7fefffffffffffff`. Both failures are proved
by kernel evaluation in `Software/TwoSumExactTests.lean`. These are limitations
of the unchanged classical algorithm, not remaining reconstruction proof gaps.

The real-format proof is in `IEEE/TwoSumExact.lean`, with the executable bridge
in `IEEE/Software/TwoSumExact.lean`. It uses `Format.sterbenz`, its signed-magnitude
form, and the representable add/sub roundoff lemmas. New rounding bounds preserve
representable endpoints and binary lattices, handle halves at the subnormal
limit, and allow exact doubled comparison values beyond the finite upper limit.
`Format.twoSum_avirt_representable` and `twoSum_bround_representable` discharge
both formerly outstanding reconstruction obligations. Sterbenz's word-level
subtraction theorem continues to cover every rounding mode with clear flags;
TwoSum itself uses nearest-even throughout.

`Software.compensatedSum I xs` is a total online compensated summation: apply
TwoSum to the high accumulator and each input, accumulate the recovered low parts
in a correction accumulator, then round `high+correction` once at the end.
`compensatedSum_spec` proves the full IEEE operation schedule and sticky flags.
`compensatedSum?` adds a rational certificate alongside the same word operations;
`compensatedSum?_execution` proves exact equality of its successful result and flags
to the total computation. It rejects failed TwoSum certificates and nonfinite
correction/final results. The certificate's rational accounting does not compute
the original exact sum to validate the answer.

For every successful certificate, `compensatedSum_error_of_certificate` bounds
the decoded total result's absolute error by its executable `errorBound`.
This radius sums the absolute local correction-rounding errors and the final
rounding error. `compensatedSum?_sound` additionally derives

```text
abs(result - S) ≤ u*abs(S) + (1+u)*(growth(u,n)*M + ε*geomWeight(u,n)) + ε
M ≤ u*H + n*ε
```

Here `S` is the exact input sum, `n` the input count, `M` the sum of absolute
recovered low parts, `H` the sum of absolute exact inputs to the high-accumulator
additions, `u` the format's unit roundoff, and `ε=minSubnormal/2`.
Substitution exposes the second-order correction contribution; the final rounding
retains a first-order term. `FP.Compensation` supplies the general proof, a gamma
variant under `n*u<1`, and the traditional relative-error specialization with
`ε=0`. The IEEE theorem derives each local error bound from the actual rounder.
The radius and mass bounds allow gradual underflow and need no smallness condition.

`compensatedSum?_success_iff_finite` now characterizes certificate success by
`CompensatedSumFinite`: finite inputs, each high addition and `bv`, each correction
addition, and the final addition. TwoSum reconstruction exactness and all its
certificate checks follow from these conditions. `compensatedSum?_complete`
therefore supplies a certificate from finite execution alone. The executable
algorithm, returned flags, and certificate layout are unchanged.

`compensatedSum_mixed_of_finite` removes the internal mass `H` from the error
bound. Put `A = sum(abs(x_i))`, `g = (1+u)^n - 1`, and
`G = sum_{k=0}^{n-1} (1+u)^k`. The new residual-mass invariant proves
`M ≤ g*A + ε*G`, giving an input-only bound for the actual result word:

```text
abs(result - S) ≤ u*abs(S) + (1+u)*(g²*A + ε*(1+g)*G) + ε
```

Under `n*u < 1`, `compensatedSum_gamma_of_finite` gives the closed form

```text
abs(result - S) ≤ u*abs(S) + (1+u)*(gamma(u,n)²*A + n*ε/(1-n*u)²) + ε
```

Both theorems hold for any valid interchange format, including fp32 and fp64.
Their `_of_decoded` interfaces accept a list of real input values and word-decoding
proofs. No normal-range condition is required. `FP.CompensationInput` contains
the shared real inequalities and the traditional `ε=0` specialization; its
second-order term is `(1+u)*g²*A` beyond final rounding.

For analytical range proofs, `CompensatedStepRange` uses the exact real inputs
to the high addition, `bv`, and correction addition:

```text
abs(s+a) < overflowThreshold
abs(roundFinite(s+a)-s) < overflowThreshold
abs(c + (s+a-roundFinite(s+a))) < overflowThreshold
```

`CompensatedSumRange` requires these at each step and also
`abs(finalHigh+finalCorrection) < overflowThreshold`. Its `.toFinite` theorem
implies certificate completeness and the `_of_range` error bounds. These are
conditions on the actual execution, rather than a static input-magnitude test
for overflow. The extra final condition is necessary: a finite pass for fp32
`[0x7f7fffff,0x72800000,0x72800000]` overflows only at the final addition.
The corresponding fp64 case and separate correction/bv overflow cases are
kernel-checked in `Software/CompensatedInputTests.lean`.

`compensatedEnclosure?` returns a rational interval enclosing the exact input sum,
with `compensatedEnclosure?_sound`. `compensatedEnclosure?_exists_of_finite`
and `compensatedSum_error_radius_of_finite` derive the enclosure and executable
radius directly from finite execution. A zero radius proves the total computation
returned the exact sum (`compensatedSum_exact_of_zero_bound`). Kernel examples prove
recovery of a lost unit in binary32 and binary64 and cover inexact virtual-addend
rounding, inexact correction accumulation, final rounding, subnormals, zero signs,
NaNs, and overflow. Neither general correct rounding nor unconditional exactness
of compensated summation is claimed.

## TwoProduct residual bounds and compensated dot products

`IEEE/ProductRoundoff.lean` proves the product-residual facts from binary
significands and lattices. `Software.twoProduct_spec` proves refinement to an
independent multiply/quiet-negate/FMA schedule, including exceptional inputs and
the sticky flag union. The existing TwoProduct algorithm and exact certificate
remain unchanged.

For finite operands and a finite nearest-even product `p`, the actual FMA
residual word decodes to `π` with

```text
abs(x*y - p - π) ≤ ε,          ε = minSubnormal/2
```

`TwoProductRange` is a decidable sufficient condition for exactness: finite
operands, `abs(x*y) < overflowThreshold`, and either a zero operand or
`scaleExponent(a)+scaleExponent(b) ≥ emin-fractionBits`. These are the exponents
of the integer-significand representation, not the unbiased normal exponents.
`certifiedTwoProduct?_of_range` proves certificate success from this condition.
`_success_iff_representable` characterizes exact-certificate success by residual
representability, assuming finite operands and a finite high product. The static
exponent condition is sufficient, not necessary.

A normal high product alone is insufficient: fp32 inputs `0x00800001` and
`0x3f800001` produce normal high word `0x00800002`, but their residual `2^-172`
rounds to zero. Kernel regressions also cover this behavior in fp64 and show
exact least-subnormal residuals at the exponent-condition boundary.

`Software.compensatedDot I a b n` executes the zero-started online Dot2 schedule,
in increasing index order, using nearest-even for every arithmetic operation:

```text
s = +0; c = +0
for i = 0, ..., n-1:
    (p, π) = TwoProduct(a[i], b[i])
    (s, σ) = TwoSum(s, p)
    t = RN(π + σ)
    c = RN(c + t)
result = RN(s + c)
```

`compensatedDot_spec` proves the independent total IEEE schedule;
`compensatedDot_flags_iff` accounts for all ten arithmetic events per pair and
the final addition. `compensatedDotList` accepts a list of pairs without length
truncation. Its numerical interface proves a bound against the sum of every
pair's exact product. Empty input returns positive zero and inspects no operands.

`compensatedDot?` and `compensatedDotList?` add rational accounting alongside the
same word operations. `compensatedDot?_execution` proves result and flag equality.
The new certificates allow an inexact FMA residual. They record its actual defect,
the losses from combining residuals and accumulating the correction, and final
rounding. They never validate against a separately computed exact dot product.

`compensatedDot?_success_iff_finite` proves success equivalent to
`CompensatedDotFinite`: finite operands, products, TwoSum high/bvirt results,
combined residuals, corrections, and final result. FMA-residual and TwoSum
reconstruction finiteness are derived. `CompensatedDotRange.toFinite` supplies
analytical operation-range conditions; these describe the actual execution and
do not assert that all finite input vectors avoid intermediate overflow.

For the actual decoded result `q`, put `S = sum(x_i*y_i)`,
`A = sum(abs(x_i*y_i))`, `g = growth(u,2*n)`, and `G = geomWeight(u,2*n)`.
`compensatedDot_mixed_of_finite` proves

```text
abs(q-S) ≤ u*abs(S) + (1+u)*(g²*A + ε*(1+g)*(G+n)) + ε
```

Under `2*n*u < 1`, `compensatedDot_gamma_of_finite` proves

```text
abs(q-S) ≤ u*abs(S) + (1+u)*(gamma(u,2*n)²*A + 3*n*ε/(1-2*n*u)²) + ε
```

Both have `_of_decoded` real-input and `_of_range` interfaces. The certificate
soundness theorem retains the sharper measured-defect contribution
`(1+g)*(ε*G+D)`, where `D` is the sum of absolute product defects.
`compensatedDot_exact_products_bound` derives `D=0` when each pair satisfies
`TwoProductRange`. The shared `FP.DotCompensation` proof also provides the
traditional `ε=0` specialization. General IEEE bounds retain gradual underflow.

`compensatedDot_mixed_backward` gives a componentwise perturbation of the first
vector with coefficient `u+(1+u)*g²`, plus the explicit absolute underflow budget.
`compensatedDotEnclosure?` encloses the exact dot product using the executable
radius; zero radius proves exactness of the total result. Neither unconditional
exactness nor correct rounding is claimed. Kernel tests cover product and
addition roundoff recovery, both correction-rounding stages, residual underflow,
signed zeros, subnormals, and distinct overflow paths in fp32 and fp64.

## Automatic compensated range and accuracy certificates

`FP.Range.checkCompensatedSum` accepts a list of input intervals.
`checkCompensatedDot` accepts two indexed interval families and a length;
`checkCompensatedDotList` accepts a list of interval pairs. Each uses exact
rational `Params.ofFormat` parameters and returns `Option AccuracyCertificate`.

A successful certificate has three fields:

- `resultInterval` encloses the actual rounded result.
- `exactInterval` encloses the exact mathematical sum or dot product across the input domain.
- `errorBound` is a rational absolute-error bound valid for every finite input covered by the intervals.

`Software.checkCompensatedSum_sound` and `checkCompensatedDot_sound` establish
these claims for the existing total IEEE executions, and derive their finite
execution conditions. `WordIn I J w` requires both finite decoding and interval
containment: NaNs and infinities do not qualify. The real-valued entry points
`compensatedSum_of_range_certificate` and `compensatedDot_of_range_certificate`
accept separate decoding and containment hypotheses. List alignment uses
`List.Forall₂`; indexed hypotheses concern only indices below the supplied length.
`checkCompensatedDotList_sound` provides the corresponding paired-list interface.

For example, one closed certificate covers every five-term fp32 sum in `[-1,1]`:

```lean
example (xs : List FP.IEEE.fp32.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => FP.IEEE.fp32.decode? w = some y) xs ys)
    (hb : List.Forall₂ FP.Range.Interval.Contains
      (List.replicate 5 ⟨-1,1⟩) ys) :
    ∃ q : ℝ,
      FP.IEEE.fp32.decode? (FP.IEEE.Software.compensatedSum FP.IEEE.fp32 xs).value = some q := by
  let bounds : List FP.Range.Interval := List.replicate 5 ⟨-1,1⟩
  have hc : (FP.Range.checkCompensatedSum
      (.ofFormat FP.IEEE.binary32) bounds).isSome = true := by decide +kernel
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨_,q,hq,_,_,_⟩ := FP.IEEE.Software.compensatedSum_of_range_certificate
    FP.IEEE.fp32 bounds xs ys hd hb hr
  exact ⟨q,hq⟩
```

The same application also supplies both interval containments and
`|q - ys.sum| ≤ r.errorBound`. The regression suite proves errors below `10^-5`
for all five-term fp32 sums and Dot2 products with operands in `[-1,1]`, and
below `10^-12` for the corresponding fp64 domains.

The checker tracks separate high and correction intervals. For TwoSum, it
bounds the residual using the local mixed rounding error, and checks `bvirt`
as the incoming operand plus that error. For TwoProduct, it allows the proved
half-subnormal decomposition defect. Correction additions, Dot2's residual
combination, and the final addition each have a separate range check.

Let `T` be the exact-expression interval and `M` the sum of input interval
radii (product-interval radii for Dot2). With `g_k=(1+u)^k-1`,
`G_k=Σ_{j<k}(1+u)^j`, and `ε=minSubnormal/2`, the uniform bounds are:

```
sum:  u*radius(T) + (1+u)*(g_n²*M + ε*(1+g_n)*G_n) + ε
Dot2: u*radius(T) + (1+u)*(g_2n²*M + ε*(1+g_2n)*(G_2n+n)) + ε
```

These formulas require no smallness condition on `n*u`. Empty inputs return
zero intervals and zero error without inspecting unused inputs. The
`_mixed_of_range_certificate` and `_gamma_of_range_certificate` theorems retain
the sharper input-dependent bounds; gamma forms retain `n*u<1` for summation
and `2*n*u<1` for Dot2. `compensatedDot_mixed_backward_of_range_certificate`
provides the existing componentwise backward interpretation with its absolute
underflow term. Completion and enclosure corollaries derive successful measured
execution certificates and exact-value enclosures from the same range certificate.

This checker is sufficient, not complete. It rejects malformed used intervals,
and may reject finite executions near the overflow threshold: even a singleton
`maxFinite` summation is a documented conservative rejection. It does not infer
relationships between distinct inputs or prove exactness of every product
residual. It supports same-format nearest-even compensated execution; the existing
result-bit and sticky-flag specification theorems continue to describe that execution.
