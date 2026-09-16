# Error models and proof foundations

The traditional relative-error dot-product theorem, its IEEE hypotheses,
and the connection from binary rounding to numerical error bounds.
For bounds that permit gradual underflow, use the
[mixed-error reduction results](Reductions.md#mixed-errors-and-certified-ranges).
The optional native bridges are described here for reference; they are not
a prerequisite for analysis against IEEE operation contracts.

## Traditional dot-product backward stability

The algorithm starts with `s₀ = 0` and computes

```
pᵢ     = round(xᵢ * yᵢ)
sᵢ₊₁   = round(sᵢ + pᵢ)
```

There is no fused multiply-add or reassociation. For `2*n*u < 1`, the result is

```
sₙ = Σᵢ₌₀ⁿ⁻¹ x'ᵢ * yᵢ
|x'ᵢ - xᵢ| ≤ γ₂ₙ * |xᵢ|
γₖ = k*u / (1 - k*u)
```

Only the first vector is perturbed. Zero input components remain zero. The
perturbed vector is real-valued, as in the usual definition of backward
stability; it need not be representable in the floating-point format.
The bound is conservative, counting at most two roundings per term. It is not
the sharper textbook `γₙ` bound. The underlying theorem also proves the bound
`(1+u)^(2*n)-1` without the smallness hypothesis.

| Theorem | Model / input |
| --- | --- |
| `FP.traditional_innerProduct_backward` | Any rounding function satisfying `RelativeError u` |
| `FP.IEEE.binary32_innerProduct_backward` | Explicit binary32 rounding, real-valued inputs |
| `FP.IEEE.binary64_innerProduct_backward` | Explicit binary64 rounding, real-valued inputs |
| `FP.IEEE.fp32_bits_innerProduct_backward` | Actual `BitVec 32` input encodings |
| `FP.IEEE.fp64_bits_innerProduct_backward` | Actual `BitVec 64` input encodings |
| `FP.Native.float32_innerProduct_backward` | Native `Float32` inputs and arithmetic |
| `FP.Native.float_innerProduct_backward` | Native `Float` inputs and arithmetic |

The bit-pattern theorems require finite input words. They decode those words
exactly, so they do not include an initial real-to-float conversion error.
Their output is the real value of the specified computation, in `Option ℝ`.

## IEEE assumptions and scope

The constants are:

| Format | Precision | Unit roundoff | Normal exponents | Least subnormal |
| --- | --- | --- | --- | --- |
| binary32 | 24 | `2^(-24)` | −126 … 127 | `2^(-149)` |
| binary64 | 53 | `2^(-53)` | −1022 … 1023 | `2^(-1074)` |

These are the binary interchange parameters described in
[NIST DLMF §3.1](https://dlmf.nist.gov/3.1). The specification follows
[IEEE 754-2019](https://dms-discourse-static.s3.dualstack.us-east-1.amazonaws.com/original/3X/b/7/b7b9c1edaf4019395d2b8315620948e240bf3f8f.pdf):
§3.3 for finite values, §3.4 for bit fields, Table 3.5 for parameters,
§4.3.1 for nearest-even rounding, and §7.4 for overflow. This correspondence
is a specification design choice reviewed against the text, not a formal
refinement theorem from the English standard.

`SafeDot` requires each **exact input to rounding** (each product and each sum)
to be either zero, or at least `minNormal` in magnitude and strictly below
`overflowThreshold`. The threshold is

```
(2^p - 1/2) * 2^(emax - (p-1)).
```

Thus exact cancellation is allowed. The assumptions are sufficient rather than
necessary: a small but exactly representable subnormal intermediate is excluded
by `SafeDot`, even though `roundFinite_exact` proves that it rounds exactly.
No rounding-error bound is included in `SafeDot`.

The finite-value projection used by these theorems maps both signs of zero
to real zero. NaNs and infinities have no finite projection, and overflow is
represented by `none`. This interface describes finite numerical values;
it does not describe NaN payloads, exception flags, or the sign of zero.
The separate [total arithmetic](Arithmetic.md) and
[total reductions](Reductions.md#total-scheduled-reductions-and-accumulated-flags)
provide result-word and flag proofs, including exceptional operands.

## Why the IEEE result is more than an abstract-model instantiation

With `f = p-1`, the exact rounding formula is

```
e = max(emin, floor(log₂ |x|)) - f
h = 2^e
roundFinite(x) = roundEven(x/h) * h.
```

`Int.log` implements the integer binary logarithm. `roundEven` uses the floor,
a comparison with one-half, and integer parity. Its error and midpoint behavior
are proved. `round?` returns this value below the overflow threshold and `none`
at or above the threshold.

The following are checked by Lean:

- `roundEven_error`: integer rounding error is at most one-half.
- `roundEven_midpoint`: midpoint ties select an even integer.
- `roundFinite_representable`: every nonoverflowing result belongs to the finite
  binary value set, including subnormals and binade carries.
- `roundFinite_nearest`: the result minimizes distance over the whole finite
  value set, including competitors in other binades.
- `roundFinite_exact`: every representable value rounds exactly.
- `roundFinite_relativeError`: the normal-range relative bound follows from
  binary spacing.
- `roundFinite_mixed_error`: for arbitrary real inputs, the unbounded-overflow
  rounding formula has error at most `u*|x| + minSubnormal/2`. To use this for an
  IEEE finite result, also establish nonoverflow.
- `value_representable`: every finite binary input word decodes to a value in
  that same finite value set.

The proof architecture separates format rounding from error accumulation.
The native bridge proves the following additional results:

- `floatValue_decode` / `float32Value_decode`: native values have exactly the
  same finite real interpretation as the explicit interchange decoder.
- `float_add_equiv` / `float32_add_equiv`: native addition agrees with `round?`.
- `float_mul_equiv` / `float32_mul_equiv`: native multiplication agrees with `round?`.
- `floatDot_equiv` / `float32Dot_equiv`: the executable sequential native dot
  product agrees with the specified `dot?` computation.

These equivalence theorems require finite operands and nonoverflow, but allow
subnormal inputs, subnormal results, and underflow to zero. They identify real
values, not the signs of zero. The native backward-stability corollaries use
the stronger `SafeDot` range conditions above, because a purely relative
backward-error bound is not generally valid through underflow.

For example, the binary64 operation theorem has the interface:

```lean
FP.Native.float_mul_equiv (a b : Float) (x y : ℝ)
  (ha : FP.Native.floatValue a = some x)
  (hb : FP.Native.floatValue b = some y)
  (hr : |x * y| < FP.IEEE.binary64.overflowThreshold) :
  FP.Native.floatValue (a * b) = FP.IEEE.binary64.round? (x * y)
```

The native dot functions are `FP.Native.floatDot` and `FP.Native.float32Dot`.
They execute native multiplication followed by native addition at each step;
their real projections are noncomputable proof-side definitions.

## Why there is no unconditional relative theorem

`underflow_dot` proves that the one-term product
`minSubnormal * (1/2)` rounds to zero. `underflow_not_backwardStable` proves that
this zero result cannot be explained by a relative perturbation of the first
input smaller than 100%. This applies to both formats. Consequently, the
pure relative stability claim needs range assumptions or a different
conclusion that allows an additive underflow term.

`FP/IEEE/Boundaries.lean` also checks concrete encodings of one, the least
subnormal, and infinity; positive and negative midpoint ties; the exact overflow
threshold; and a concrete admissible inner-product trace.

## Files and trust

| File | Contents |
| --- | --- |
| `FP/Basic.lean` | Relative error, products of error factors, exponential and gamma bounds |
| `FP/InnerProduct.lean` | Algorithm, local trace conditions, backward stability |
| `FP/IEEE/Rounding.lean` | Integer nearest-even rounding and lattice lemmas |
| `FP/IEEE/Format.lean` | Format constants, real rounding, single-operation relative bound |
| `FP/IEEE/Representation.lean` | Representability, nearest-point, exactness, mixed error |
| `FP/IEEE/Encoding.lean` | Binary interchange bit fields and finite decoding |
| `FP/IEEE/InnerProduct.lean` | IEEE finite-value stability |
| `FP/IEEE/WordInnerProduct.lean` | Binary32/binary64 bit-input stability |
| `FP/IEEE/Boundaries.lean` | Counterexample and boundary checks |
| `FP/Native/Rounding.lean` | Round/sticky-bit semantics and integer rounding equivalence |
| `FP/Native/Exponent.lean` | Native target exponent equals specification quantum exponent |
| `FP/Native/Normalize.lean` | Native normalization equals real nearest-even rounding |
| `FP/Native/Canonical.lean` | Normalization invariants and exactness |
| `FP/Native/Packing.lean` | Packing/unpacking round trip for canonical finite values |
| `FP/Native/Unpack.lean` | Native bit decoding equals the explicit interchange decoder |
| `FP/Native/Finite.lean` | Packing preserves representable real values |
| `FP/Native/Operations.lean` | Generic native addition/multiplication refinement |
| `FP/Native/Bridge.lean` | Public `Float`/`Float32` operation equivalence |
| `FP/Native/InnerProduct.lean` | Executable native dots, equivalence, backward stability |
| `FP/MixedError.lean` | Mixed-error decomposition, composition, and recurrence bounds |
| `FP/MixedBackward.lean` | Mixed backward stability and dot-product residual bounds |
| `FP/Summation.lean` | Reduction trees, schedule proofs, summation error and stability bounds |
| `FP/IEEE/Summation.lean`, `FP/IEEE/MixedDot.lean` | Explicit IEEE summation and mixed dot semantics |
| `FP/Range/Interval.lean` | Rational interval operations and format-parameter correspondence |
| `FP/Range/Checker.lean` | Executable sum/dot certificates and their soundness proofs |
| `FP/Native/Summation.lean`, `FP/Native/MixedDot.lean` | Native algorithms and certificate-based error theorems |
| `FP/MixedBoundaries.lean` | Kernel-checked certificate and mixed-error boundary examples |
| `FP/Verification.lean` | Axiom regression checks |

There are no proof placeholders or project axioms. The checked main theorems
use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
No native evaluation proof oracle is used. The real-valued specification is
noncomputable; this is compatible with kernel-checked proofs.

For comparison, [FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec)
is a broader Lean port of Flocq and uses a different pinned toolchain. It was
reviewed as a possible dependency, but is not imported here. Lean's
[native floating-point documentation](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/)
describes the logical model targeted by the bridge.

The remaining implementation trust boundary is Lean's compiler and runtime:
`Float.add` and `Float.mul` (and their `Float32` counterparts) have logical
bodies and external implementations. These proofs verify the logical bodies,
not generated C, processor instructions, or runtime floating-point settings.
The bridge does not establish complete exceptional-value propagation,
overflow behavior, NaN payloads, or exception flags. Those are outside its
finite, nonoverflowing hypotheses.
