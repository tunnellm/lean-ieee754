# IEEE 754-2019 binary32/binary64 coverage

This is the implementation ledger for the agreed completion plan. **The full
plan is not complete.** The project has no theorem asserting full IEEE conformance.
A checked foundation or a finite-value theorem does not close an operation's
result-bit and exception obligations. Native Lean refinement is an optional
complement and is no longer a completion requirement.

## Target and fixed choices

The primary target is executable software refinement to the formal IEEE
specification, followed by numerical-analysis theorems. Existing native proofs
are retained, but opaque or missing native APIs do not block completion.

- Binary32 and binary64, default exception handling, explicit evaluation order.
- Proof-first executable integer/rational reference algorithms; no host arithmetic
  or external testing oracle in proofs.
- Five rounding modes; nearest-even by default. Tininess after rounding, uniformly.
- Signed zeros, infinities, signaling/quiet NaNs, and all payload bits retained.
- Arithmetic NaN selection: first signaling operand, otherwise first quiet operand;
  preserve selected sign/payload and quiet it. Default NaN: positive, quiet, payload zero.
- Precision conversion aligns high payload bits. Invalid integer conversion
  clamps to destination bounds, NaN maps to zero, and invalid is set.
- FMA's zero-times-infinity case raises invalid even with a quiet-NaN third operand.
- `Int32` is the associated `logB`/`scaleB` integer format. Exceptional integer
  `logB` returns `Int32.min` and raises invalid.
- Decimal arithmetic formats, optional Clause 9 operations, alternate/trapping
  handlers, compiler correctness, and hardware conformance are outside this target.
  Decimal and hexadecimal **text conversion are inside** the target.

The governing text is [IEEE 754-2019](https://dms-discourse-static.s3.dualstack.us-east-1.amazonaws.com/original/3X/b/7/b7b9c1edaf4019395d2b8315620948e240bf3f8f.pdf).
The English-to-formal specification correspondence requires review, separately
from checking proofs of the formal statements. The [working group's revision
notes](https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/) help
distinguish required operations from recommendations.

## Implemented foundations and operation families

Names below are relative to `FP.IEEE` except names beginning with `FP.Native`.
All public additions are reachable from `import FP`.

| Area | Implementation and checked results | Remaining obligation |
| --- | --- | --- |
| §3 binary encoding | `Interchange.Fields.pack/unpack`; `pack_unpack`, `unpack_pack`; total `Interchange.Datum` | None for lossless field representation |
| §3 full datum encoding | `Datum.encode_decode`, `decode_encode`, `encode_injective`; constrained constructors for all classes | None for representation round trips |
| Existing finite decoder | Executable `Datum.toRat?`; `toRat?_cast`, `toRat?_decode` | None for finite projection compatibility |
| §4 integer rounding | `Software.roundInt` implements all five modes; directed extremality, nearest-point/error, midpoint parity/away rules | Integration with total binary result encoding and exceptions |
| Binary grid selection | `Software.quantumExponent`, `quantum`; `log_abs_cast`, `quantum_cast` | Total all-mode rounding proof over representable floating-point values |
| Existing RNE rounding | `scaledRound_even_cast`, `roundNearest?_cast`, `roundNearest?_representable` | Finite projection retained; total refinement below |
| Exact finite encoder | `encodeFinite?_sound`, `findCoefficient_complete`, `encodeFinite_spec`; bounded exponent search and integer normalization | Optional performance optimization |
| Total RNE rounding | `Software.roundNearest`, `roundNearest_spec`: actual result words, signs, signed overflow infinities and all five flags against `Spec.NearestRounding` | Further arithmetic families |
| RNE range events and projection | `precisionRound_cast`, `tinyAfter_spec`, `roundNearest_projection`; after-precision tininess, exact tiny results unflagged, compatibility with finite rounder | Integrated into total scheduled reductions |
| All-mode real refinement | `roundInt_cast`, `scaledRound_cast`, `precisionRoundWithMode_cast`; independent `Spec.roundInteger` and `Spec.roundWithMode` | Final rounding-clause audit, including whole finite-set extremality/tie characterization for the additional modes |
| All-mode range events and flags | `overflowWithMode_spec`, `tinyWithMode_spec`, `roundingFlags_spec`; unbounded-exponent precision rounding; range flags imply inexact | Further arithmetic families |
| All-mode overflow delivery | `overflowResult_spec`; mode/sign-dependent infinity or maxFinite, with exactly overflow and inexact | Integrated into `roundWithMode`; operator wrappers remain open |
| All-mode finite representability | `scaledRound_representable`; absence of unbounded-exponent overflow implies representability, including carry | None for this encoding precondition |
| Total all-mode word rounding | `roundWithMode`, `roundWithMode_spec` against independent `Spec.Rounding`; words, signed zeros, all flags, every rational input | Further arithmetic families |
| Nearest-even overflow equivalence | `overflowWithMode_even_iff`, `overflow_even_real_iff`: midpoint and unbounded-exponent criteria agree for every exact rational input, including signed ties | Extension to arbitrary real exact inputs if needed for future irrational-operation contracts |
| Nearest-even endpoint equivalence | `roundWithMode_even_eq`: full result equality (bits and all flags), no range assumption; `_projection`, `_cast` give the original finite models | Further arithmetic families |
| Nearest-even numerical transfer | `roundWithMode_even_mixed_error` with `u*abs(x) + minSubnormal/2`; `_relativeError` under the original `Safe` condition | Integrated for nearest-even reductions |
| All-mode numerical results | `scaledRound_exact`, directed lattice extremality, `roundWithMode_projection`, `roundWithMode_mixed_error` with `2*u*abs(x) + minSubnormal` | Whole reduction bounds for additional modes |
| Total same-format arithmetic | `Software.add`, `sub`, `mul`, `binary_spec`, `add_spec`, `sub_spec`, `mul_spec` against independent `Spec.Arithmetic`; all modes, every operand encoding, result bits and flags | Mixed arithmetic is implemented below; final clause audit |
| Arithmetic special results | NaN selection preserves original operand payload/sign; invalid infinities and zero-times-infinity; signed-zero rules; `nanResult_spec`, `invalidResult_spec` | Remaining arithmetic families |
| Arithmetic finite refinement | `binary_finite`, `binary_even_projection`, `binary_even_cast`; exact operation then one rounding, including overflow in the projection | Integrated for nearest-even reductions |
| Arithmetic numerical transfer | `binary_even_mixed_error`, `binary_mixed_error` on decoded result words, assuming finite inputs and no overflow | Whole reduction bounds for additional modes |
| Total binary format conversion | `convert`, `convert_spec`, `convert_finite`, `convert_even_projection`; all fp32/fp64 source/destination pairs and modes; special values, signs, result bits and flags | Final conversion-clause audit |
| Exact finite widening | `convert32To64_exact`: every finite fp32 encoding widens exactly in every mode without flags; representable-set embedding | None for finite fp32-to-fp64 value/flag exactness |
| Cross-format NaN payloads | `convertNaN_spec`, `alignedPayload_roundtrip`, `convertNaN_payload_roundtrip`; high-bit alignment, quieting, source sign, lossless widen/narrow payload round trips | Binding policy audit; other mappings are not implemented |
| Mixed source/destination arithmetic | `mixedAdd`, `mixedSub`, `mixedMul`, `mixedBinary_spec`; independent source and destination formats, all modes, special results and flags | Final arithmetic-clause audit; mixed-precision reduction schedules |
| Mixed arithmetic numerical transfer | `mixedBinary_finite` proves exact source operation then one destination rounding; `_even_projection`, `_even_mixed_error`, `_mixed_error`; same-format finite compatibility | Further reduction bounds and schedules |
| Total division | `div`, `mixedDiv`, `div_spec`, `mixedDiv_spec` against independent `Spec.Division`; all source/destination formats, modes, operand classes, result bits and flags | Final division-clause audit; native refinement remains optional |
| Division exception predicates | `mixedDiv_divideByZero_iff`: finite nonzero / zero only; `mixedDiv_invalid_iff`: signaling NaNs, zero/zero, infinity/infinity | Integrated into total division |
| Division numerical transfer | `mixedDiv_finite`: exact rational quotient then one destination rounding; `_even_projection`, `_even_cast`, mixed bounds; `_even_backward` gives a numerator perturbation under `Safe` | Further algorithm-level composition; qualifications retained |
| Total fused multiply-add | `fma`, `mixedFma`, `fma_spec`, `mixedFma_spec` against independent `Spec.Fma`; exact product-plus-sum and one rounding, all classes/modes/formats/flags; explicit zero-times-infinity with NaN policy | Final arithmetic-clause and binding audit |
| FMA numerical transfer | `mixedFma_finite`, `_even_cast`, `_mixed_error`, `_even_mixed_error`, `_even_backward`; multiplicand/addend perturbation bounded by destination unit roundoff under `Safe` | Algorithm-level composition; qualifications retained |
| Arbitrary-real rounding foundations | `Spec.roundInteger_nearest_error`, `roundWithMode_representable`, `roundWithMode_mixed_error`; representability from the unbounded-exponent overflow predicate | Available for irrational operations |
| Exact square-root algorithm | `sqrtRoundInt_spec`, `log_sqrt`, `sqrtScaled_cast`, `sqrtPrecision_cast`; integer square root and squared midpoint tests equal real sqrt rounding | No approximate sqrt or native oracle |
| Total square root | `sqrt`, `mixedSqrt`, `roundSqrt_spec`, `sqrt_spec`, `mixedSqrt_spec` against independent `Spec.Sqrt`; signed zeros, negative inputs, NaNs/infinities, every mode and all flags | Final square-root-clause and binding audit; native refinement optional |
| Square-root numerical transfer | `mixedSqrt_zero`, `mixedSqrt_positive`, `_mixed_error`, `_even_mixed_error`, `_even_relativeError`, `_even_backward`; radicand perturbation at most `2*u+u²` | Positive finite inputs and stated range qualifications; zero has exact theorem |
| Directed global extremality | `Spec.roundWithMode_up_le`, `roundWithMode_le_down`; optimality against the whole finite value set | Used for intervals and adjacent values |
| Adjacent values | `nextUp`, `nextDown`; `_finite_spec` proves strict adjacency or infinity when no finite neighbor exists; `next_nan`, `next_infinity`, `next_flags` | Final clause/binding audit; finite signed-zero words follow the rounder, with boundary regressions |
| Certified finite intervals | `enclose_sound`, `enclose_tight`, `intervalAdd_sound`, `intervalMul_sound`; actual outward-rounded endpoint words and endpoint-operation flags | Extended-real endpoints and further interval operations; existing algorithm range certificates retained |
| Power-of-two scaling | `scaleB`, `mixedScaleB_spec`, `representable_scale`, `mixedScaleB_exact`; all modes, source/destination formats and special operands | Huge-exponent shortcuts and final clause/binding audit |
| Exactness certificates and normalization | `roundWithMode_exact`, `exactScale?_sound`, `finiteExponent?_bounds`, `normalized?_spec`, `normalizeWord?_sound` | IEEE floating-result logB remains separate; normalization success is checked, not asserted for every format |
| FMA product-residual schedule | `twoProduct_spec` against independent `Spec.TwoProduct`; multiplication, quiet negation, FMA, and sticky flags | Total software schedule checked; native refinement optional |
| Exact FMA product residual | `certifiedTwoProduct?_sound`, `_complete`, `_of_range`, `_success_iff_representable`; `TwoProductRange` derives exactness from finite inputs/product and decoded exponents | Static exponent condition is sufficient, not necessary; residual underflow can prevent exactness |
| Bounded FMA product residual | `twoProduct_bounded_of_finite`, `productResidual_isFinite`; finite product implies finite residual and decomposition defect at most `minSubnormal/2` | Requires finite operands/high product; normal high product alone does not ensure exactness |
| Classical TwoSum execution | `twoSum`, `twoSum_spec`, `twoSum_flags`; independent six-operation IEEE schedule and exact sticky flag union | Schedule proof is total; numerical exactness has the qualifications below |
| General TwoSum exact decomposition | `twoSum_exact_of_finite_stages`, `_of_finite`, `_of_range`: actual high/low words decode to the rounded sum and exact residual; no reconstruction assumptions | Inputs, initial sum, and bvirt must be finite; initial-sum finiteness alone is false, with fp32/fp64 counterexamples |
| Exact cancellation | `Format.sterbenz`, `_abs`; `Software.sub_sterbenz`, `_abs`: every mode, clear flags, zeros/subnormals included | Finite decoded operands satisfying factor-of-two conditions |
| Representable add/sub roundoff | `Format.roundFinite_add_residual_representable`, `_sub_residual_representable`; word-level `add_residual_representable`, `sub_residual_representable` | Word results must be finite; existence of a residual does not establish algorithmic reconstruction |
| TwoSum reconstruction and flags | `Format.twoSum_avirt_representable`, `twoSum_bround_representable`; word-level `_reconstruction_values_of_finite_stages`, `_reconstruction_flags_of_finite_stages`, `_flags_of_finite_stages` | Remaining four stages are exact and finite; only sum/bvirt contribute flags |
| TwoSum certificate completeness | `certifiedTwoSum?_of_finite_stages`, `_success_iff_finite_stages`, `_of_range`; previous sufficient-condition interfaces retained | Success is equivalent to finite inputs/sum/bvirt; executable checks unchanged |
| Total compensated summation | `compensatedSum_spec` against independent `Spec.CompensatedSumEvaluation`; online high/low correction schedule and all flags | Not a general correct-rounding or exact-sum claim |
| Certified compensated error bounds | `compensatedSum?_sound`, `_execution`, `compensatedSum_error_of_certificate`; actual result/flag equality, executable absolute radius and residual-mass bounds through underflow | Existing certificate API retained; success follows from finite execution below |
| Compensated certificate completeness | `compensatedSum?_success_iff_finite`, `_complete`; corresponding step/pass equivalences | Finite inputs, high/bvirt, correction and final additions; reconstruction checks are derived |
| Input-only compensated bounds | `compensatedSum_mixed_of_finite`, `_gamma_of_finite`, `_mixed_of_decoded`, `_gamma_of_decoded`; residual mass bounded by `g*A+ε*G`, yielding second-order `g²*A` and explicit underflow terms | Actual total nearest-even result; gamma form additionally needs `n*u<1` |
| Compensated operation-range conditions | `CompensatedSumRange.toFinite`, `compensatedSum?_complete_of_range`, `_mixed_of_range`, `_gamma_of_range` | Exact real inputs to high/bvirt/correction/final operations lie below the overflow threshold; no normal-range restriction |
| Compensated enclosures and exactness | `compensatedEnclosure?_sound`, `_exists_of_finite`, `compensatedSum_error_radius_of_finite`, `compensatedSum_exact_of_zero_bound`; rational enclosure and zero-radius exactness | Further interval consumers |
| Traditional compensation analysis | `FP.compensation_second_order`, `_gamma`, `compensation_relative_bound`; `CompensationInput` adds input-mass bounds, closed gamma form and `ε=0` specialization | IEEE instantiation derives operation errors from rounding; final rounding included |
| Total online Dot2 | `compensatedDot`, `compensatedDotList`, `_spec`, `_flags_iff`; independent zero-started indexed schedule and all ten arithmetic events per pair | Same format and nearest-even; no unconditional exactness or correct-rounding claim |
| Dot2 certificate completeness | `compensatedDot?_execution`, `_success_iff_finite`, `_complete`; `CompensatedDotRange.toFinite` and `_complete_of_range` | Requires finite products, high/bvirt, combined residuals, corrections and final addition; product residuals may be inexact |
| Dot2 input-only accuracy | `compensatedDot_mixed_of_finite`, `_gamma_of_finite`, real-decoding and operation-range variants; second-order `growth(u,2*n)²*A` with explicit absolute underflow terms | Gamma bound requires `2*n*u<1`; input-interval discharge is checked below |
| Dot2 sharper and backward bounds | `compensatedDot?_sound` retains measured defect mass; `_exact_products_bound` derives zero defects; `_mixed_backward` gives componentwise perturbations plus an absolute residual | Pure `FP.dot_compensation_relative_bound` specializes to `ε=0`; general IEEE claims retain underflow |
| Dot2 enclosures and exactness | `compensatedDot_error_radius_of_finite`, `compensatedDotEnclosure?_sound`, `_exists_of_finite`, `_exact_of_zero_bound`; paired-list bounds and exactness interface | Further interval consumers and mixed-precision schedules |
| Automatic compensated range proofs | `Range.checkCompensatedSum`, `checkCompensatedDot`, `checkCompensatedDotList`; word-level soundness derives operation ranges, finite execution, and result containment for every covered finite input | Same format, nearest-even; sufficient checking with conservative rejection; no cross-input correlation tracking |
| Uniform compensated accuracy certificates | `AccuracyCertificate`, `sumAccuracyBound_sound`, `dotAccuracyBound_sound`; rational bounds across whole domains, exact-expression intervals, real-decoding and paired-list interfaces | Underflow terms retained; no length smallness requirement for default bounds; empty inputs have zero error |
| Range-to-analysis composition | `_mixed_of_range_certificate`, `_gamma_of_range_certificate`, Dot2 `_mixed_backward_of_range_certificate`; measured-certificate completion and enclosure corollaries | Gamma variants retain their size conditions; native refinement and mixed-precision compensated schedules remain separate |
| §5.5.1 quiet sign operations | `Software.copy`, `copySign`, `negate`, `abs`; whole-field preservation, involution/idempotence, no flags | Optional native bit-level refinement modulo native NaN canonicalization |
| §5.7 classification | `Software.classify`, `isFinite`, `isNaN`, `isSignaling`, `isInfinite`, `isZero`, `isNormal`, `isSubnormal`, `isSignMinus`, `isCanonical`, `radix`; `isFinite_spec` | Optional native refinement; version queries below are separate |
| §5.11 comparisons | `orderedValue`, `compareDatum`, `Relation`, `Software.compare`; unordered characterization, finite ordering, signed-zero equality, invalid-only flag policy | Final standard table audit; native comparison refinement is optional |
| §6 NaN construction | `quietFraction`, `makeQuietNaN`, `defaultNaN`; quietness, nonzero fraction, payload preservation, idempotence | Implemented by the conversion family below |
| §6 NaN propagation | `selectNaN`, `propagateNaN`; quiet result, selected sign/payload, signaling-input invalid | Integration with each arithmetic operation's invalid conditions |
| §4/§5.6 environment | `Env.setMode`, raise/lower/test/save/restore; `Flags.test_iff`, mask behavior | Final clause-by-clause environment binding audit |
| §7 sticky flags | `Result.bind`, `Env.run`; associativity, sticky monotonicity, `Env.run_bind` | Integrated for implemented arithmetic; remaining operation families |
| Native add/multiply (optional) | Existing `float{32,}_{add,mul}_equiv` | Total special/overflow result-bit refinement |
| Native subtraction (optional) | `FP.Native.float_sub_equiv`, `float32_sub_equiv`; full unpacked `sub_unpacked_eq_add_neg` | Packed refinement still assumes finite operands and nonoverflow |
| Native inexact rounding (optional) | `FP.Native.roundWithAccuracy_value_of_represents`, `roundWithAccuracy_canonical_of_represents` | Callers must establish positive mantissa, `Represents`, and exponent precondition; zero initial mantissa needs separate handling |
| Native division residual (optional) | `FP.Native.quotient_represents` | `divCore` scale/exponent/range obligations and full operator/packing proof |
| Native sqrt residual (optional) | `FP.Native.sqrt_residual_represents` | `sqrtCore` scale/exponent/range obligations and full operator/packing proof |
| Executable reductions | `sumTree?_cast`, `sequentialSum?_cast`, `pairwiseSum?_cast`, `dot?_cast`; includes overflow propagation | Finite interface retained; total scheduled interface below |
| Raw input reductions | `wordSumTree?_cast`, `wordDot?_cast` from actual input encodings, assuming finite used inputs | Finite interface retained; total scheduled interface below |
| Complementary numerical proofs | Rational and raw-word certificate theorems give a finite result, enclosure, and mixed bounds; rational dot/sum pure backward theorems retain stronger range hypotheses | Additional rounding modes; nearest-even total integration is checked below |
| Total scheduled reductions | `sumTree`, `sequentialSum`, `pairwiseSum`, `dot`; `sumTree_spec`, `dot_spec` against independent arithmetic evaluation relations; all modes and operand classes | Mixed formats and numerical bounds for additional modes; not the optional Clause 9 reduction APIs |
| Exact sticky-flag accounting | `sumTree_flags_iff`, `dot_flags_iff`; a flag is set iff an executed operation raised it; explicit event lists | Further evaluation bindings |
| Total finite-result compatibility | `sumTree_projection_of_some`, `dot_projection_of_some`; success of the old finite evaluator implies the same decoded total result | No unconditional claim equating old `none` with total exceptional behavior |
| Total numerical bounds | Sum/tree/sequential/pairwise and dot `_mixed_of_certificate`; dot gamma variant; pure `sequentialSum_backward`, `pairwiseSum_backward`, `dot_backward` on result words | Nearest-even only; original range/size qualifications retained |
| Existing numerical analysis | Traditional, IEEE finite, native dot/sum, mixed errors, range certificates retained | Integrated for nearest-even total scheduled reductions |

## Mandatory completion checklist still open

The rows are operation families, not an assertion that each row is one theorem.
Each must be expanded into individual result, rounding, exception, and binding
obligations when its implementation is added.

| Requirement | Work still required |
| --- | --- |
| §4 and §7 total rounding | All-mode exact-rational word/flag refinement is checked. Remaining: whole finite-set extremality/tie characterizations for additional modes; arbitrary-real overflow equivalence if required for irrational operations; final standard audit |
| §5.4.1 add/subtract/multiply | Same-format and mixed source/destination total operators and result/flag proofs are checked. Remaining: final standard/binding audit |
| §5.4.1 divide | Total same/mixed-format result and flag proofs are checked. Remaining: final standard/binding audit; native core/packed refinement is optional |
| §5.4.1 squareRoot | Total implementation and word/flag refinement checked above. Remaining: final clause/binding audit; native refinement optional |
| §5.4.1 fusedMultiplyAdd | Total implementation and word/flag refinement checked above. Remaining: final clause/binding audit; no native bridge required |
| §5.3.1 integral rounding | Explicit direction variants and exact-reporting variant, result words and flags |
| §5.3.1 nextUp/nextDown | Executable neighbors, finite-set adjacency including infinity boundaries, NaN handling and flag proofs checked above. Remaining: final signed-zero/binding clause audit |
| §5.3.1 remainder | Exact nearest-even quotient remainder, sign of zero, exceptional cases |
| §5.3.3 scaleB/logB | Total scaleB and certified finite exponent/normalization helpers checked above. Remaining: IEEE floating-result logB exceptional semantics, huge-exponent shortcuts and clause audit |
| §5.4.1/§5.8 integer conversion | Width-parametric signed/unsigned conversions in both directions; exact-reporting variants; invalid result policy; native bridges are optional |
| §5.4.2 format conversion | Total all-pair/mode refinement, exact finite widening, one-round finite conversion and payload/signaling handling are checked. Remaining: final conversion/binding audit |
| §5.4.2/§5.12 decimal text | Grammar, parser, formatter, requested precision/mode, exceptions, signed specials, 9/17-digit round trips, extreme exponents |
| §5.4.3/§5.12 hex text | Grammar, exact parser/formatter and specified-precision conversion, specials and round trips |
| §5.7.1 version predicates | Audited version-specific compatibility results, then truthful 1985/2008/2019 queries; no placeholder `true` or unproved `false` |
| §5.10 totalOrder/totalOrderMag | Total ordering including signed zeros and NaN type/payload ordering; distinguish from numeric comparison |
| §6 special arithmetic results | Operation-specific signed-zero and infinity behavior; NaN policy integration and allowed-result proofs |
| §7 default exceptions | Full generation and handling proofs for all five exceptions; exact tiny results distinguished from flagged underflow |
| §10/§11 binding and evaluation | Explicit format/mode/order behavior, composition and reproducibility audit for the supported library binding |
| Final conformance records | Construct only after every applicable IEEE obligation is proved; no assumptions of operator error or refinement |
| Differential validation | Pinned SoftFloat test-only harness with mode/tininess alignment and explicit NaN-policy handling; not a theorem oracle |

## Validation and acceptance gates

`FP/IEEE/Software/Boundaries.lean` checks both formats' ten classes, payload-preserving
sign operations, NaN comparison/propagation behavior, signed zeros and infinities,
all integer rounding modes at signed ties, subnormal midpoints, overflow boundaries,
and saved/sticky flags. `Software/ReductionTests.lean` also checks schedule-sensitive
cancellation, overflow propagation, unused exceptional inputs, raw-word underflow,
and complete certificate-to-error-bound examples. `Software/NearestTests.lean` checks
actual binary32/binary64 encodings and flags at signed zero, exact subnormals,
half-subnormal ties, overflow ties, and after-rounding tininess boundaries.
`Software/RoundingModesTests.lean` exercises all five modes at signed overflow,
exact and inexact tiny inputs, signed zero, ordinary ties and binade carry, and
checks the distinction between inexact maxFinite and flagged overflow.
`Software/ProductBoundsTests.lean` checks exact least-subnormal residuals at the
static exponent boundary, half-subnormal losses immediately below it, normal high
products with residual underflow, and the distinction between sufficient static
conditions and actual exactness. `Software/CompensatedDotTests.lean` checks
product/addition roundoff recovery, residual-combination and correction losses,
underflow accepted with a measured defect, exact zero-radius real results, and
product/high/bvirt/correction/final overflow. Both formats instantiate the general
theorems without assuming successful runtime certificates.
`Software/ArithmeticTests.lean` checks NaN priority and payload preservation,
subtraction's NaN sign, invalid combinations, infinity signs, all-mode zero rules,
finite ties, exact/inexact underflow, overflow and sticky composition.
`Software/TotalReductionTests.lean` checks schedule-dependent cancellation in both
formats, empty/singleton semantics, signaling-NaN use, underflow retained after
addition, overflow followed by invalid, directed zero signs, and a complete
certificate-to-total-result error theorem. `Software/ConversionTests.lean` checks
payload widening/narrowing, signaling NaNs with truncated payloads, signed specials,
exact finite widening, narrowing ties and range flags, mixed arithmetic NaN priority,
and a cancellation example that would fail with early operand conversion.
`Software/DivisionTests.lean` checks signed special cases, exact divideByZero/invalid
policies, recurring quotients in every mode, exact/inexact subnormals, overflow,
NaN priority, mixed-format division without early divisor conversion, and sticky
flags through a later invalid operation.
`Software/FMATests.lean` checks single-rounding residuals, cancellation that avoids
intermediate overflow, ternary NaN priority, the zero-times-infinity/quiet-NaN policy,
signed zeros, midpoint modes, underflow and mixed-source cancellation.
`Software/SqrtTests.lean` checks irrational square roots in all modes and both formats,
signed zeros, negative inputs, infinities, NaN conversion, exact extreme subnormals,
mixed-format overflow/underflow, midpoint parity and precision-rounding tininess.
`Software/NumericalToolsTests.lean` checks adjacent-value boundaries and flags,
scaling and normalization at extreme exponents, finite outward-rounded intervals,
invalid enclosure rejection, and checked FMA product decompositions, including
underflow rejection. It also supplies a real-valued `1/3` enclosure certificate.
`Software/CompensatedTests.lean` checks classical TwoSum without magnitude ordering,
inexact bvirt, signed zeros/subnormals, rejection of nonfinite/overflowing paths,
unit recovery under cancellation in both formats, correction-rounding losses and
final-rounding losses. End-to-end zero-radius certificates prove exact real results
for the total IEEE computation.
The earlier boundary suite exhaustively executes the representation on a six-bit toy
format. General theorems, rather than these examples, establish universal correctness.

`FP/Verification.lean` guards axiom dependencies. Accepted dependencies remain a
subset of `propext`, `Classical.choice`, and `Quot.sound`; no project axioms,
`sorry`, or native-evaluation proof oracle are permitted. Run `lake build` and
`lake build fp` before closing any milestone.

Division, FMA, and square root now have total software word/flag refinement proofs.
Adjacent values, certified finite intervals, power-of-two scaling/normalization,
exact and bounded FMA product residuals, general TwoSum exactness and certificate
completeness, compensated summation, and online Dot2 with proved error bounds
are now available for numerical analysis.
The remaining implementation gates cover the other auxiliary operations, integer/text conversions,
additional algorithm schedules/modes, differential validation, and the final conformance audit.
Binary conversion and mixed-source/destination add/subtract/multiply now have
total refinement proofs, including the explicit NaN payload conversion policy.
Same-format scheduled reductions now have total evaluation/flag proofs and
nearest-even numerical bounds. Further rounding-mode accuracy and the remaining
conversion, text and conformance obligations remain open.
The old and new nearest-even APIs now have unconditional result equality for
all exact rational inputs. Exact encoding, all-mode word/flag refinement,
and nonoverflow finite projection compatibility are now available. The later operator, conversion,
text, and conformance gates remain open as listed above.

`Software/CancellationTests.lean` checks all five rounding modes on adjacent
normal fp32/fp64 values whose difference is the least subnormal, including
negative inputs. It also applies the symbolic all-mode Sterbenz theorem at the
factor-of-two boundary, derives TwoSum certificate success from cancellation
hypotheses, and instantiates residual representability at a halfway addition.

`Software/TwoSumExactTests.lean` applies the general theorem to arbitrary fp32/fp64
inputs and checks cases with both reconstruction corrections nonzero, midpoint
absorption, operand order, sign symmetry, inexact bvirt, signed zeros, and exact
least-subnormal cancellation. Kernel theorems also exhibit finite initial sums
whose bvirt subtraction overflows, proving why the second range condition is needed.

`Software/CompensatedRangeTests.lean` checks uniform certificates for arbitrary
five-term fp32/fp64 sums and Dot2 inputs in `[-1,1]`, derives numerical bounds
without assumed operation traces, and covers signed zeros, subnormals, cancellation,
residual underflow, malformed inputs, unused indices, threshold equality,
correction/final checks, and known overflow cases. It also proves that some finite
executions are conservatively rejected and that exceptional words cannot satisfy
finite interval containment. All closed certificates use `decide +kernel`.
