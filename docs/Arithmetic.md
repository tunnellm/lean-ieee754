# IEEE arithmetic reference

Reference for the binary32/binary64 representation, rounding, and operation
proofs. Start with [Using FP](Using.md) to apply the numerical theorems.
The [coverage ledger](../IEEE754Coverage.md) records the precise conformance
scope and open obligations.

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
