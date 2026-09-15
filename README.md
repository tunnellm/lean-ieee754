# FP: IEEE 754 and numerical analysis in Lean

Lean 4 tools for numerical error analysis, from traditional floating-point
models to explicit IEEE 754 binary32/binary64 words. The library proves
componentwise backward stability for inner products, error bounds through
gradual underflow, and certified accuracy for sequential, pairwise, and
compensated reductions.

The executable integer/rational arithmetic includes total add, subtract,
multiply, divide, FMA, and square root, with result-bit and exception-flag
proofs against formal specification relations. Numerical reduction bounds
currently use round-to-nearest, ties-to-even, with explicit evaluation order
and range hypotheses or executable certificates. The IEEE rounding-error
bound is proved from binary rounding.

**Scope:** this is a numerical-analysis research library, not a completed
IEEE 754 conformance claim. The [coverage ledger](IEEE754Coverage.md) records
the remaining operation families and specification-audit obligations.
The optional native `Float`/`Float32` bridges verify Lean's logical bodies
under their stated finite/nonoverflow conditions; they do not verify generated
machine code or processor behavior.

## Start here

The supported toolchain is Lean **4.33.1**. The mathlib revision and its
transitive dependencies are pinned in the package configuration and manifest.
From a checkout with Lean/Elan installed:

```sh
lake exe cache get
lake build
lake build fp
```

`lake build` checks the library, regression examples, and principal-theorem
axiom guards. `import FP` exposes the public toolkit without importing those
tests or guards. Specific modules can also be imported individually.

- [Use FP in another Lean project](docs/Using.md), including guidance for a
  proof-writing agent and a starting point for Krylov-method work.
- [Three buildable downstream examples](examples/consumer/README.md): abstract
  dot-product stability, an IEEE dot-product certificate, and fp64 compensated
  summation with a concrete accuracy bound.
- [Contribution and verification guide](CONTRIBUTING.md).
- [Release and Zenodo procedure](docs/Releasing.md) and
  [release notes](CHANGELOG.md).

The remaining sections describe the formal models and theorem families in detail.

## License

FP is distributed under the [Apache License 2.0](LICENSE). Dependencies retain
their respective licenses; their source checkouts are not included in this
repository.

## Citation

To cite the version of the proofs you used, see Zenodo (link pending).

![Zenodo DOI pending](https://img.shields.io/badge/Zenodo-DOI_pending-lightgrey)

<!-- Replace the pending link and badge with the Zenodo concept DOI after archival. -->

## Total IEEE formalization: implementation in progress

The full binary32/binary64 completion plan is **not yet implemented**. The
[coverage ledger](IEEE754Coverage.md) records checked work and every remaining
operation family; the project does not currently assert full IEEE conformance.

The new executable foundations include:

- Lossless field packing and total decoding, with inverse proofs preserving
  signed zeros, infinities, and quiet/signaling NaN payloads.
- Exact rational finite projection, proved equal to the original real decoder.
- All five integer rounding modes and scaled rational rounding; the nearest-even
  specialization provably agrees with the existing finite IEEE specification.
- Quiet sign operations, classification, quiet/signaling comparison truth tables,
  and deterministic NaN propagation with payload preservation.
- Explicit rounding-mode and sticky-flag state with save/restore and composition proofs.
- Native subtraction refinement under the existing finite/nonoverflow conditions.
- Native rounding value/canonicality proofs for inexact accuracy information with
  a positive initial mantissa; exact quotient/remainder and integer-square-root
  residual interpretation. Complete native division and square-root refinement
  remains optional; total software division, FMA, and square root are checked below.

These APIs are under `FP.IEEE.Interchange`, `FP.IEEE.Software`, and `FP.IEEE.Env`.
For example, `Software.roundNearest? binary32 q` computes the existing finite
nearest-even projection using exact rational arithmetic. Its `none` result
represents overflow. The new `Software.roundNearest fp32 q` (or `fp64`)
returns actual result bits and operation-local exception flags.
`Software.compare` takes two formats, a quiet/signaling policy, and a `Relation`
truth table, returning a Boolean value and operation-local flags.

Addition, subtraction, multiplication, division, FMA, and square root now have
total software result-bit/flag proofs. Remaining auxiliary operations, integer/text
conversions, optional native bridges, and final conformance records remain open.
The existing stability results retain their stated qualifications.

## Total nearest-even rounding

`Software.roundNearest fp32 q` returns `Result fp32.Word`: `.value` contains
IEEE bits and `.flags` reports each of the five exceptions. An optional Boolean
argument selects the sign of an exact zero. Nonzero inputs rounded to zero retain
their sign; overflow returns signed infinity with overflow and inexact flags.
Inputs are exact rationals, so this interface does not yet handle NaN or infinity
operands of arithmetic operations.

`roundNearest_spec` proves refinement to the independent real-valued contract
`Spec.NearestRounding`, including every flag. Underflow requires both inexactness
and tininess after precision rounding with an unbounded exponent range. Exact
subnormals do not raise underflow. Testing only the final result's class would
miss some tiny computations that produce the smallest normal result.

`encodeFinite_spec` proves exact encoding, backed by completeness for every
representable rational. The reference encoder searches the bounded exponent
range and normalizes an integer coefficient. `roundNearest_projection` proves
that decoding the total result recovers the previous `roundNearest?` interface,
providing the connection for subsequent integration with reduction proofs.

Total arithmetic operators and scheduled reductions are described below.
The formal overflow contract uses the existing
nearest-even midpoint threshold. Its equivalence to the unbounded-exponent
range test is now proved for every exact rational input.

## Total rounding in all five modes

`Software.roundWithMode fp32 mode q` (or `fp64`) now returns actual result words
and operation-local flags for every exact rational input in all five modes.
For example, `.towardZero` returns signed maxFinite on overflow, whereas
`.nearestAway` returns signed infinity. The optional final Boolean controls
the sign of an exact zero input.

`roundWithMode_spec` proves refinement to the independent real-valued
`Spec.Rounding` contract. Overflow and after-rounding tininess are classified
using precision rounding with an unbounded exponent range. Merely exceeding
maxFinite in exact magnitude does not always raise overflow: a toward-zero
result can still round back to maxFinite without overflow, while raising inexact.
`scaledRound_representable` proves finite encoding is possible whenever this
overflow test is false, including significand carry and gradual underflow.

`roundWithMode_projection` recovers the rational rounded value when there is
no overflow. `roundWithMode_mixed_error` supplies a decoded result and the bound
`2*u*abs(x) + minSubnormal` for every mode. The sharper nearest-mode half-quantum
bound remains available. Additional checked results give directed extremality
on the selected lattice and exactness of all modes on representable inputs.

This endpoint uses the unbounded-exponent overflow definition directly. The
older `roundNearest` endpoint retains its midpoint-threshold contract.
`overflowWithMode_even_iff` proves that the tests coincide for every exact rational
input, including both signs of the exact overflow midpoint. This yields
`roundWithMode_even_eq`: equality of the entire result, including bits and flags,
with no range assumption. `roundWithMode_even_projection` and
`roundWithMode_even_cast` connect the new endpoint to the original rational and
real finite projections, including overflow.

The new endpoint also inherits the sharper nearest-even bound
`u*abs(x) + minSubnormal/2` through `roundWithMode_even_mixed_error` and the original
relative-error theorem under `Format.Safe` through `roundWithMode_even_relativeError`.
These supply the local rounding connection for the existing reduction proofs.
Same-format add/subtract/multiply now handle special operands as described below.
Total scheduled reductions return words and sticky flags. The final
clause-by-clause conformance audit is still pending.

## Total addition, subtraction and multiplication

`Software.add fp32 mode a b`, `Software.sub`, and `Software.mul` take actual
interchange words and return a word plus operation-local flags. The same APIs
work with `fp64`. `add_spec`, `sub_spec`, and `mul_spec` prove total refinement
to the independent real-valued `Spec.Arithmetic` contract, without finite-input
or nonoverflow assumptions.

The operations handle signed zeros, infinities, quiet/signaling NaNs and payload
selection. Opposite effective infinities in addition/subtraction and zero times
infinity return the default quiet NaN with invalid. Subtraction adjusts the
second operand's numeric sign while preserving its original NaN sign/payload.
Exact cancellation produces negative zero only in toward-negative mode;
combining like-signed zeros preserves their sign. Finite results use one exact
rational operation and one rounding in the destination format.

`binary_finite` proves that last statement directly. `binary_even_projection`
and `binary_even_cast` recover the original nearest-even finite models, including
overflow. `binary_even_mixed_error` and `binary_mixed_error` give decoded-result
bounds through underflow when overflow is absent. `Result.bind` accumulates
flags across calls; the arithmetic tests include overflow followed by invalid.

These operators use the same source and destination format. The mixed-format
APIs below choose the two sources and destination independently. Total reductions
currently compose the same-format operators.

## Format conversion and mixed-precision arithmetic

`Software.convert fp32 fp64 mode w` converts a word between formats. `convert_spec`
proves the total real-valued conversion contract for all four source/destination
pairs and all five modes, including signed zeros, infinities, NaNs and flags.
`convert32To64_exact` proves every finite fp32 value widens exactly with no flags
in every mode. `convert_finite` proves finite conversions perform one destination
rounding, and `convert_even_projection` recovers the nearest-even finite model.

NaN conversion preserves the source sign, quiets signaling NaNs, and raises only
invalid for signaling inputs. The chosen binding aligns high payload bits,
appending zeros when widening and discarding low bits when narrowing. This is
our specified payload policy, not a uniquely mandated IEEE mapping.
`convertNaN_spec` proves the output payload formula; `convertNaN_payload_roundtrip`
proves widening followed by narrowing preserves every original payload bit.

`Software.mixedAdd A B D mode a b`, `mixedSub`, and `mixedMul` allow independently
selected source formats `A`, `B` and destination `D`, covering all eight fp32/fp64
combinations. Their `_spec` theorems cover every operand encoding and flag.
`mixedBinary_finite` proves the exact source values are combined before a single
destination rounding; no operand is first rounded into the destination format.
NaN priority is resolved before payload conversion or subtraction's sign change.

`mixedBinary_even_projection`, `mixedBinary_even_mixed_error`, and
`mixedBinary_mixed_error` supply finite-model and numerical connections, with
unit roundoff and underflow scale determined by the destination. The bounds
retain finite-input and nonoverflow qualifications. Mixed-precision reduction
schedules are not yet provided.

## Total division

`Software.div fp32 mode a b` and `Software.mixedDiv A B D mode a b` return
actual quotient words and operation-local flags. `div_spec` and `mixedDiv_spec`
prove total refinement to the independent `Spec.Division` contract for all
fp32/fp64 source/destination combinations and rounding modes.

The exception characterizations are explicit: `mixedDiv_divideByZero_iff`
requires a finite nonzero dividend and a zero divisor. Infinity divided by
zero produces correctly signed infinity without flags. `mixedDiv_invalid_iff`
characterizes signaling NaNs, zero/zero and infinity/infinity. NaN priority and
cross-format payload handling use the established conversion policy.

`mixedDiv_finite` proves that finite inputs with a nonzero divisor undergo exact
rational division and one destination rounding, without early operand conversion.
The `_even_projection` and `_even_cast` theorems recover the finite models,
including overflow. `_mixed_error` and `_even_mixed_error` allow gradual underflow
when the quotient does not overflow. Under the original `Safe` quotient condition,
`mixedDiv_even_backward` expresses the decoded result as
`(x*(1+δ))/y`, with `abs(δ) ≤ destination.unitRoundoff`.

## Total fused multiply-add and square root

`Software.fma I mode a b c` and `mixedFma A B C D mode a b c` compute the
exact product-plus-addend with one destination rounding. `fma_spec` and
`mixedFma_spec` prove result-word and five-flag refinement to independent
`Spec.Fma`, for every operand encoding and all five modes. Intermediate product
overflow is avoided when the exact fused result fits. The binding raises invalid
for zero times infinity even with a quiet-NaN addend; ternary NaN selection uses
the first signaling operand, otherwise the first quiet operand.

`mixedFma_finite` and `_even_cast` connect finite operands to the real rounding
model. The mixed-error theorems permit gradual underflow when the fused result
does not overflow. Under `Safe` on the exact result, `_even_backward` gives
`r = (x*(1+δ))*y + z*(1+δ)` with `abs(δ) ≤ destination.unitRoundoff`.

`Software.sqrt I mode a` and `mixedSqrt A D mode a` refine independent `Spec.Sqrt`
without operand or range assumptions. They preserve negative zero, reject negative
nonzero operands, and implement the established NaN conversion policy. The finite
algorithm uses `Nat.sqrt` and exact rational squared-midpoint comparisons.
`sqrtRoundInt_spec`, `log_sqrt`, `sqrtScaled_cast`, and `sqrtPrecision_cast` prove
agreement with mathematical `Real.sqrt`, including irrational results. No approximate
square-root oracle or assumed rounding property is used. `roundSqrt_spec` proves
both the result and all flags, with after-rounding tininess determined by
unbounded-exponent precision rounding.

For positive finite inputs, `mixedSqrt_mixed_error` and `_even_mixed_error` bound
the decoded result's error by `2*u*sqrt(q) + minSubnormal` and
`u*sqrt(q) + minSubnormal/2`, respectively, assuming no overflow. With the additional
`Safe` condition on the exact square root, `_even_backward` gives
`r = sqrt(q*(1+θ))` with `abs(θ) ≤ 2*u + u²`. Signed-zero exactness has a separate
all-mode theorem, `mixedSqrt_zero`.

`FMATests` and `SqrtTests` use kernel evaluation for cancellation, single-rounding
ties, special values, payload selection, exact and inexact subnormals, overflow,
and the distinction between precision-rounding tininess and final result class.
These arithmetic families are complete at the software-contract level; the broader
IEEE completion ledger still includes auxiliary operations, text/integer conversions,
and the final clause-by-clause conformance audit.

## Numerical analysis tools: intervals, neighbors, scaling, and product residuals

`Software.nextUp I a` and `nextDown I a` compute adjacent values for `fp32` or
`fp64`. `nextUp_finite_spec` and `nextDown_finite_spec` prove strict ordering and
minimality/maximality against **every finite representable value**, including the
case where no finite neighbor exists and the result is infinity. Separate theorems
cover NaN conversion, infinity inputs and flags: only signaling NaNs raise invalid;
stepping between maxFinite and infinity raises neither overflow nor inexact.
The implementation uses exact half-minSubnormal probes and directed rounding.
It does not enumerate the encoding space or invoke host floating-point arithmetic.

`Spec.roundWithMode_up_le` and `roundWithMode_le_down` establish whole-format
extremality for directed rounding. `Software.enclose I J` uses these results to
produce tight outward-rounded word endpoints for an exact rational interval `J`.
`enclose_sound` proves containment of every real member of `J`; `enclose_tight`
proves endpoint optimality. `intervalAdd` and `intervalMul` compose these enclosures,
with soundness theorems for actual endpoint words. Reversed intervals, nonfinite
input endpoints, and unavailable finite output bounds produce `none`. The API
currently supports finite enclosures, not extended-real infinity endpoints.
Endpoint rounding flags are returned; input intervals themselves are pairs of words.

`Software.scaleB I mode a n` and `mixedScaleB A D mode a n` compute exact
multiplication by `2^n` before one destination rounding. `mixedScaleB_spec` proves
all-mode refinement, including special operands and range flags. `representable_scale`
and `mixedScaleB_exact` prove exactness when the shifted significand/exponent fits.
`exactScale?` rejects nonfinite inputs and any flagged scaling; its soundness theorem
certifies the exact real value. `finiteExponent?` and `normalized?` extract an
exponent and an exact rational significand with magnitude in `[1,2)`.
`normalizeWord?` additionally returns a checked, exactly scaled IEEE word and the
reconstruction exponent, including for subnormal inputs. These exponent helpers are
not the IEEE floating-result `logB` operation. Scaling is a reference algorithm;
huge integer-exponent shortcuts remain future work.

`Software.twoProduct` computes a nearest-even product and its FMA residual.
`certifiedTwoProduct?` returns the pair only when the high part is finite and the
residual has no flags. `certifiedTwoProduct?_sound` proves `x*y = high+low` exactly.
The high multiplication may be inexact, and its flags remain in the returned result.
`certifiedTwoProduct?_complete` proves success when the exact residual is
representable. `certifiedTwoProduct?_of_range` now derives that property from
finite inputs, a nonoverflowing exact product, and a sufficient condition on the
decoded exponents. `twoProduct_bounded_of_finite` proves that a finite product
has a finite FMA residual with decomposition defect at most `minSubnormal/2`.
Residual underflow can still cause the exact certificate to fail; the bounded
theorem and compensated dot-product certificates account for that loss below.

`NumericalToolsTests` includes kernel checks in both formats for binade and
zero/subnormal boundaries, infinities, NaN signs/payloads, normalization of extreme
values, outward rounding of `1/3`, mixed-sign interval multiplication, rejected
invalid enclosures, and exact/inexact product-residual certificates. A complete
example uses the certificate theorem to enclose the mathematical real number `1/3`.

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

## Build and use

Lean is pinned to `v4.33.1`; mathlib is pinned in `lakefile.toml` and
`lake-manifest.json`.

```sh
lake update
lake exe cache get
lake build
lake build fp
```

Import `FP` for the public definitions and theorems. Regression and boundary
examples are collected in `FP.Verification`, which is an explicit default
build target. CI runs `lake build FP FP.Verification fp` and then builds the
separate example package in `examples/consumer`.

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

### Automatic compensated range and accuracy certificates

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

## The theorem

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

The finite-value specification projects both signs of zero to real zero.
All-ones exponent fields (NaNs and infinities) have no finite projection.
Overflow is represented by `none`. There are no claims about NaN payloads,
exception flags, traps, zero sign, other rounding modes, flush-to-zero,
extended intermediate precision, or compiler contraction to FMA.
The bit-input dot product rejects exceptional operands; it does not attempt to
reproduce their complete IEEE propagation rules.

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
requested relative stability claim needs range assumptions or a different
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
