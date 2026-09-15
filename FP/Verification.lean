import FP.IEEE.Boundaries
import FP.Native.InnerProduct
import FP.MixedBoundaries
import FP.IEEE.Software.Boundaries
import FP.IEEE.Software.ReductionTests
import FP.IEEE.Software.NearestTests
import FP.IEEE.Software.RoundingModesTests
import FP.IEEE.Software.NearestEquivalence
import FP.IEEE.Software.ArithmeticTests
import FP.IEEE.Software.TotalReductionTests
import FP.IEEE.Software.ConversionTests
import FP.IEEE.Software.DivisionTests
import FP.IEEE.Software.FMATests
import FP.IEEE.Software.SqrtTests
import FP.IEEE.Software.NumericalToolsTests
import FP.IEEE.Software.CompensatedTests
import FP.IEEE.Software.CancellationTests
import FP.IEEE.Software.TwoSumExactTests
import FP.IEEE.Software.CompensatedInputTests
import FP.IEEE.Software.ProductBoundsTests
import FP.IEEE.Software.CompensatedDotTests
import FP.IEEE.Software.CompensatedRangeTests

/-! These guards fail the build if the principal results acquire extra axioms. -/

/-- info: 'FP.traditional_innerProduct_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.traditional_innerProduct_backward

/-- info: 'FP.IEEE.fp32_bits_innerProduct_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.fp32_bits_innerProduct_backward

/-- info: 'FP.IEEE.fp64_bits_innerProduct_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.fp64_bits_innerProduct_backward

/-- info: 'FP.IEEE.Format.roundFinite_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_representable

/-- info: 'FP.IEEE.Format.roundFinite_nearest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_nearest

/-- info: 'FP.IEEE.Format.underflow_not_backwardStable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.underflow_not_backwardStable

/-- info: 'FP.Native.float_add_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float_add_equiv

/-- info: 'FP.Native.float_mul_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float_mul_equiv

/-- info: 'FP.Native.float32_add_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32_add_equiv

/-- info: 'FP.Native.float32_mul_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32_mul_equiv

/-- info: 'FP.Native.floatDot_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.floatDot_equiv

/-- info: 'FP.Native.float32Dot_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32Dot_equiv

/-- info: 'FP.Native.float_innerProduct_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float_innerProduct_backward

/-- info: 'FP.Native.float32_innerProduct_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32_innerProduct_backward

/-- info: 'FP.mixedError_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.mixedError_decomposition

/-- info: 'FP.recurrence_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.recurrence_bound

/-- info: 'FP.ReductionTree.mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.ReductionTree.mixed_error

/-- info: 'FP.sequentialSum_backward_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.sequentialSum_backward_gamma

/-- info: 'FP.pairwiseSum_backward_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.pairwiseSum_backward_gamma

/-- info: 'FP.roundedDot_mixed_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.roundedDot_mixed_backward

/-- info: 'FP.Range.checkSum_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.checkSum_sound

/-- info: 'FP.Range.checkDot_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.checkDot_sound

/-- info: 'FP.IEEE.Format.dot?_mixed_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.dot?_mixed_backward

/-- info: 'FP.Native.floatSequentialSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.floatSequentialSum_mixed_of_certificate

/-- info: 'FP.Native.floatPairwiseSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.floatPairwiseSum_mixed_of_certificate

/-- info: 'FP.Native.float32SequentialSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32SequentialSum_mixed_of_certificate

/-- info: 'FP.Native.float32PairwiseSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32PairwiseSum_mixed_of_certificate

/-- info: 'FP.Native.floatDot_mixed_gamma_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.floatDot_mixed_gamma_of_certificate

/-- info: 'FP.Native.float32Dot_mixed_gamma_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32Dot_mixed_gamma_of_certificate

/-- info: 'FP.Examples.float_underflow_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Examples.float_underflow_mixed

/-- info: 'FP.Examples.float32_underflow_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Examples.float32_underflow_mixed

/-- info: 'FP.IEEE.Interchange.Datum.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Interchange.Datum.encode_decode

/-- info: 'FP.IEEE.Interchange.Datum.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Interchange.Datum.decode_encode

/-- info: 'FP.IEEE.Interchange.Datum.toRat?_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Interchange.Datum.toRat?_decode

/-- info: 'FP.IEEE.Software.roundInt_nearest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundInt_nearest

/-- info: 'FP.IEEE.Software.roundInt_even_midpoint_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundInt_even_midpoint_even

/-- info: 'FP.IEEE.Software.roundInt_away_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundInt_away_midpoint

/-- info: 'FP.IEEE.Software.roundNearest?_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundNearest?_cast

/-- info: 'FP.IEEE.Software.sign_operations_preserve_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sign_operations_preserve_fraction

/-- info: 'FP.IEEE.Software.compareDatum_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compareDatum_finite

/-- info: 'FP.IEEE.Software.compareDatum_unordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compareDatum_unordered

/-- info: 'FP.IEEE.Software.propagateNaN_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.propagateNaN_selected

/-- info: 'FP.IEEE.Env.run_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Env.run_bind

/-- info: 'FP.Native.float_sub_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float_sub_equiv

/-- info: 'FP.Native.float32_sub_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.float32_sub_equiv

/-- info: 'FP.Native.roundWithAccuracy_value_of_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.roundWithAccuracy_value_of_represents

/-- info: 'FP.Native.roundWithAccuracy_canonical_of_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.roundWithAccuracy_canonical_of_represents

/-- info: 'FP.Native.quotient_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.quotient_represents

/-- info: 'FP.Native.sqrt_residual_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Native.sqrt_residual_represents

/-- info: 'FP.IEEE.Software.sumTree?_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree?_cast

/-- info: 'FP.IEEE.Software.dot?_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot?_cast

/-- info: 'FP.IEEE.Software.sumTree?_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree?_mixed_of_certificate

/-- info: 'FP.IEEE.Software.dot?_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot?_mixed_of_certificate

/-- info: 'FP.IEEE.Software.wordSumTree?_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordSumTree?_cast

/-- info: 'FP.IEEE.Software.wordDot?_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDot?_cast

/-- info: 'FP.IEEE.Software.wordSumTree?_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordSumTree?_mixed_of_certificate

/-- info: 'FP.IEEE.Software.wordDot?_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDot?_mixed_of_certificate

/-- info: 'FP.IEEE.Software.sequentialSum?_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sequentialSum?_backward

/-- info: 'FP.IEEE.Software.pairwiseSum?_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.pairwiseSum?_backward

/-- info: 'FP.IEEE.Software.dot?_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot?_backward

/-- info: 'FP.IEEE.Software.encodeFinite?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.encodeFinite?_sound

/-- info: 'FP.IEEE.Software.findCoefficient_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.findCoefficient_complete

/-- info: 'FP.IEEE.Software.encodeFinite_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.encodeFinite_spec

/-- info: 'FP.IEEE.Software.precisionRound_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.precisionRound_cast

/-- info: 'FP.IEEE.Software.roundNearest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundNearest_spec

/-- info: 'FP.IEEE.Software.roundNearest_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundNearest_projection

/-- info: 'FP.IEEE.Software.roundInt_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundInt_cast

/-- info: 'FP.IEEE.Software.scaledRound_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.scaledRound_cast

/-- info: 'FP.IEEE.Software.scaledRound_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.scaledRound_exact

/-- info: 'FP.IEEE.Software.scaledRound_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.scaledRound_mixed_error

/-- info: 'FP.IEEE.Software.roundingFlags_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundingFlags_spec

/-- info: 'FP.IEEE.Software.overflowResult_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.overflowResult_spec

/-- info: 'FP.IEEE.Software.scaledRound_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.scaledRound_representable

/-- info: 'FP.IEEE.Software.roundWithMode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_spec

/-- info: 'FP.IEEE.Software.roundWithMode_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_projection

/-- info: 'FP.IEEE.Software.roundWithMode_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_mixed_error

/-- info: 'FP.IEEE.Software.overflowWithMode_even_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.overflowWithMode_even_iff

/-- info: 'FP.IEEE.Software.roundWithMode_even_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_even_eq

/-- info: 'FP.IEEE.Software.overflow_even_real_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.overflow_even_real_iff

/-- info: 'FP.IEEE.Software.roundWithMode_even_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_even_projection

/-- info: 'FP.IEEE.Software.roundWithMode_even_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_even_cast

/-- info: 'FP.IEEE.Software.roundWithMode_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_even_mixed_error

/-- info: 'FP.IEEE.Software.roundWithMode_even_relativeError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_even_relativeError

/-- info: 'FP.IEEE.Software.binary_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_spec

/-- info: 'FP.IEEE.Software.add_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.add_spec

/-- info: 'FP.IEEE.Software.sub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sub_spec

/-- info: 'FP.IEEE.Software.mul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mul_spec

/-- info: 'FP.IEEE.Software.binary_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_finite

/-- info: 'FP.IEEE.Software.binary_even_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_projection

/-- info: 'FP.IEEE.Software.binary_even_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_cast

/-- info: 'FP.IEEE.Software.binary_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_mixed_error

/-- info: 'FP.IEEE.Software.binary_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_mixed_error

/-- info: 'FP.IEEE.Software.sumTree_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree_spec

/-- info: 'FP.IEEE.Software.dot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_spec

/-- info: 'FP.IEEE.Software.sumTree_flags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree_flags_iff

/-- info: 'FP.IEEE.Software.dot_flags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_flags_iff

/-- info: 'FP.IEEE.Software.sumTree_projection_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree_projection_of_some

/-- info: 'FP.IEEE.Software.dot_projection_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_projection_of_some

/-- info: 'FP.IEEE.Software.sumTree_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sumTree_mixed_of_certificate

/-- info: 'FP.IEEE.Software.sequentialSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sequentialSum_mixed_of_certificate

/-- info: 'FP.IEEE.Software.pairwiseSum_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.pairwiseSum_mixed_of_certificate

/-- info: 'FP.IEEE.Software.dot_mixed_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_mixed_of_certificate

/-- info: 'FP.IEEE.Software.dot_mixed_gamma_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_mixed_gamma_of_certificate

/-- info: 'FP.IEEE.Software.dot_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_backward

/-- info: 'FP.IEEE.Software.sequentialSum_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sequentialSum_backward

/-- info: 'FP.IEEE.Software.pairwiseSum_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.pairwiseSum_backward

/-- info: 'FP.IEEE.Software.convertNaN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convertNaN_spec

/-- info: 'FP.IEEE.Software.convert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convert_spec

/-- info: 'FP.IEEE.Software.convert_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convert_finite

/-- info: 'FP.IEEE.Software.convert_even_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convert_even_projection

/-- info: 'FP.IEEE.Software.alignedPayload_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.alignedPayload_roundtrip

/-- info: 'FP.IEEE.Software.convertNaN_payload_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convertNaN_payload_roundtrip

/-- info: 'FP.IEEE.Software.convert32To64_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.convert32To64_exact

/-- info: 'FP.IEEE.Software.mixedBinary_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_spec

/-- info: 'FP.IEEE.Software.mixedAdd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedAdd_spec

/-- info: 'FP.IEEE.Software.mixedSub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSub_spec

/-- info: 'FP.IEEE.Software.mixedMul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedMul_spec

/-- info: 'FP.IEEE.Software.mixedBinary_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_finite

/-- info: 'FP.IEEE.Software.mixedBinary_even_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_even_projection

/-- info: 'FP.IEEE.Software.mixedBinary_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_even_mixed_error

/-- info: 'FP.IEEE.Software.mixedBinary_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_mixed_error

/-- info: 'FP.IEEE.Software.mixedBinary_same_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedBinary_same_finite

/-- info: 'FP.IEEE.Software.mixedDiv_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_spec

/-- info: 'FP.IEEE.Software.div_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.div_spec

/-- info: 'FP.IEEE.Software.mixedDiv_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_finite

/-- info: 'FP.IEEE.Software.mixedDiv_even_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_even_projection

/-- info: 'FP.IEEE.Software.mixedDiv_even_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_even_cast

/-- info: 'FP.IEEE.Software.mixedDiv_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_even_mixed_error

/-- info: 'FP.IEEE.Software.mixedDiv_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_mixed_error

/-- info: 'FP.IEEE.Software.mixedDiv_divideByZero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_divideByZero_iff

/-- info: 'FP.IEEE.Software.mixedDiv_invalid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_invalid_iff

/-- info: 'FP.IEEE.Software.mixedDiv_even_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedDiv_even_backward

/-- info: 'FP.IEEE.Spec.roundInteger_nearest_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Spec.roundInteger_nearest_error

/-- info: 'FP.IEEE.Spec.roundWithMode_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Spec.roundWithMode_representable

/-- info: 'FP.IEEE.Spec.roundWithMode_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Spec.roundWithMode_mixed_error

/-- info: 'FP.IEEE.Software.fma_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.fma_spec

/-- info: 'FP.IEEE.Software.mixedFma_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_spec

/-- info: 'FP.IEEE.Software.mixedFma_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_finite

/-- info: 'FP.IEEE.Software.mixedFma_even_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_even_cast

/-- info: 'FP.IEEE.Software.mixedFma_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_mixed_error

/-- info: 'FP.IEEE.Software.mixedFma_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_even_mixed_error

/-- info: 'FP.IEEE.Software.mixedFma_even_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedFma_even_backward

/-- info: 'FP.IEEE.Software.sqrtRoundInt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sqrtRoundInt_spec

/-- info: 'FP.IEEE.Software.log_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.log_sqrt

/-- info: 'FP.IEEE.Software.sqrtScaled_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sqrtScaled_cast

/-- info: 'FP.IEEE.Software.sqrtPrecision_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sqrtPrecision_cast

/-- info: 'FP.IEEE.Software.roundSqrt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundSqrt_spec

/-- info: 'FP.IEEE.Software.sqrt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sqrt_spec

/-- info: 'FP.IEEE.Software.mixedSqrt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_spec

/-- info: 'FP.IEEE.Software.mixedSqrt_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_positive

/-- info: 'FP.IEEE.Software.mixedSqrt_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_mixed_error

/-- info: 'FP.IEEE.Software.mixedSqrt_even_mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_even_mixed_error

/-- info: 'FP.IEEE.Software.mixedSqrt_even_relativeError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_even_relativeError

/-- info: 'FP.IEEE.Software.mixedSqrt_even_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedSqrt_even_backward

/-- info: 'FP.IEEE.Spec.roundWithMode_up_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Spec.roundWithMode_up_le

/-- info: 'FP.IEEE.Spec.roundWithMode_le_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Spec.roundWithMode_le_down

/-- info: 'FP.IEEE.Software.noOverflow_of_abs_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.noOverflow_of_abs_le_max

/-- info: 'FP.IEEE.Software.roundWithMode_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_exact

/-- info: 'FP.IEEE.Software.roundWithMode_exact_of_no_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.roundWithMode_exact_of_no_flags

/-- info: 'FP.IEEE.Software.representable_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.representable_gap

/-- info: 'FP.IEEE.Software.mixedScaleB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedScaleB_spec

/-- info: 'FP.IEEE.Software.mixedScaleB_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.mixedScaleB_exact

/-- info: 'FP.IEEE.Software.exactScale?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.exactScale?_sound

/-- info: 'FP.IEEE.Software.finiteExponent?_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.finiteExponent?_bounds

/-- info: 'FP.IEEE.Software.normalized?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.normalized?_spec

/-- info: 'FP.IEEE.Software.normalizeWord?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.normalizeWord?_sound

/-- info: 'FP.IEEE.Software.enclose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.enclose_sound

/-- info: 'FP.IEEE.Software.enclose_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.enclose_tight

/-- info: 'FP.IEEE.Software.intervalAdd_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.intervalAdd_sound

/-- info: 'FP.IEEE.Software.intervalMul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.intervalMul_sound

/-- info: 'FP.IEEE.Software.nextUp_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.nextUp_adjacent

/-- info: 'FP.IEEE.Software.nextDown_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.nextDown_adjacent

/-- info: 'FP.IEEE.Software.nextUp_finite_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.nextUp_finite_spec

/-- info: 'FP.IEEE.Software.nextDown_finite_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.nextDown_finite_spec

/-- info: 'FP.IEEE.Software.next_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.next_flags

/-- info: 'FP.IEEE.Software.next_nan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.next_nan

/-- info: 'FP.IEEE.Software.next_infinity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.next_infinity

/-- info: 'FP.IEEE.Software.certifiedTwoProduct?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoProduct?_sound

/-- info: 'FP.IEEE.Software.certifiedTwoProduct?_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoProduct?_complete

/-- info: 'FP.compensation_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_step

/-- info: 'FP.compensation_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_finish

/-- info: 'FP.compensation_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_second_order

/-- info: 'FP.compensation_second_order_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_second_order_gamma

/-- info: 'FP.compensation_relative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_relative_bound

/-- info: 'FP.IEEE.Software.twoSum_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_spec

/-- info: 'FP.IEEE.Software.twoSum_checked_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_checked_exact

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_sound

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_complete

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_exact_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_exact_sum

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_absorbed

/-- info: 'FP.IEEE.Software.twoSum_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_flags

/-- info: 'FP.IEEE.Software.binary_even_error_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_error_of_decode

/-- info: 'FP.IEEE.Software.compensatedPass?_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedPass?_valid

/-- info: 'FP.IEEE.Software.compensatedSum?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_sound

/-- info: 'FP.IEEE.Software.compensatedAux?_finite_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedAux?_finite_inputs

/-- info: 'FP.IEEE.Software.compensatedCore_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedCore_spec

/-- info: 'FP.IEEE.Software.compensatedSum_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_spec

/-- info: 'FP.IEEE.Software.compensatedSum?_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_execution

/-- info: 'FP.IEEE.Software.compensatedSum_error_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_error_of_certificate

/-- info: 'FP.IEEE.Software.compensatedSum_exact_of_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_exact_of_zero_bound

/-- info: 'FP.IEEE.Software.compensatedEnclosure?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedEnclosure?_sound

/-- info: 'FP.IEEE.Format.sterbenz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.sterbenz

/-- info: 'FP.IEEE.Format.sterbenz_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.sterbenz_abs

/-- info: 'FP.IEEE.Format.roundFinite_add_residual_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_add_residual_representable

/-- info: 'FP.IEEE.Format.roundFinite_sub_residual_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_sub_residual_representable

/-- info: 'FP.IEEE.Software.sub_sterbenz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sub_sterbenz

/-- info: 'FP.IEEE.Software.sub_sterbenz_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sub_sterbenz_abs

/-- info: 'FP.IEEE.Software.add_residual_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.add_residual_representable

/-- info: 'FP.IEEE.Software.sub_residual_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.sub_residual_representable

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_two_reconstructions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_two_reconstructions

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_cancellation

/-- info: 'FP.IEEE.Format.roundFinite_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_neg

/-- info: 'FP.IEEE.Format.half_le_roundFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.half_le_roundFinite

/-- info: 'FP.IEEE.Format.roundFinite_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_lattice

/-- info: 'FP.IEEE.Format.twoSum_bvirt_exact_of_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.twoSum_bvirt_exact_of_abs_le

/-- info: 'FP.IEEE.Format.twoSum_avirt_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.twoSum_avirt_representable

/-- info: 'FP.IEEE.Format.twoSum_bround_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.twoSum_bround_representable

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_finite_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_finite_stages

/-- info: 'FP.IEEE.Software.twoSum_exact_of_finite_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_exact_of_finite_stages

/-- info: 'FP.IEEE.Software.twoSum_reconstruction_values_of_finite_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_reconstruction_values_of_finite_stages

/-- info: 'FP.IEEE.Software.twoSum_reconstruction_flags_of_finite_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_reconstruction_flags_of_finite_stages

/-- info: 'FP.IEEE.Software.twoSum_flags_of_finite_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_flags_of_finite_stages

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_success_iff_finite_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_success_iff_finite_stages

/-- info: 'FP.IEEE.Software.twoSum_exact_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_exact_of_finite

/-- info: 'FP.IEEE.Software.certifiedTwoSum?_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoSum?_of_range

/-- info: 'FP.IEEE.Software.twoSum_exact_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoSum_exact_of_range

/-- info: 'FP.compensation_input_mass_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_input_mass_step

/-- info: 'FP.compensation_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_input_bound

/-- info: 'FP.mul_geomWeight_eq_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.mul_geomWeight_eq_growth

/-- info: 'FP.geomWeight_le_gamma_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.geomWeight_le_gamma_den

/-- info: 'FP.compensation_input_gamma_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_input_gamma_bound

/-- info: 'FP.compensation_input_relative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.compensation_input_relative_bound

/-- info: 'FP.IEEE.Software.compensatedStep?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedStep?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedAux?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedAux?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedPass?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedPass?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedSum?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedSum?_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_complete

/-- info: 'FP.IEEE.Software.compensatedSum_error_radius_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_error_radius_of_finite

/-- info: 'FP.IEEE.Software.compensatedEnclosure?_exists_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedEnclosure?_exists_of_finite

/-- info: 'FP.IEEE.Software.wordListAbsSum_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordListAbsSum_cast

/-- info: 'FP.IEEE.Software.compensatedStep?_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedStep?_input_bound

/-- info: 'FP.IEEE.Software.compensatedAux?_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedAux?_input_bound

/-- info: 'FP.IEEE.Software.compensatedPass?_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedPass?_input_bound

/-- info: 'FP.IEEE.Software.compensatedSum?_residual_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_residual_mass_bound

/-- info: 'FP.IEEE.Software.compensatedSum_mixed_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_mixed_of_finite

/-- info: 'FP.IEEE.Software.compensatedSum_gamma_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_gamma_of_finite

/-- info: 'FP.IEEE.Software.compensatedSum_mixed_of_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_mixed_of_decoded

/-- info: 'FP.IEEE.Software.compensatedSum_gamma_of_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_gamma_of_decoded

/-- info: 'FP.IEEE.Software.CompensatedStepRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedStepRange.toFinite

/-- info: 'FP.IEEE.Software.CompensatedPassRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedPassRange.toFinite

/-- info: 'FP.IEEE.Software.CompensatedPassFinite.result_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedPassFinite.result_finite

/-- info: 'FP.IEEE.Software.CompensatedSumRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedSumRange.toFinite

/-- info: 'FP.IEEE.Software.compensatedSum?_complete_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum?_complete_of_range

/-- info: 'FP.IEEE.Software.compensatedSum_mixed_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_mixed_of_range

/-- info: 'FP.IEEE.Software.compensatedSum_gamma_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_gamma_of_range

/-- info: 'FP.IEEE.Format.roundFinite_residual_representable_of_wide_lattice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_residual_representable_of_wide_lattice

/-- info: 'FP.IEEE.Format.roundFinite_small_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_small_error

/-- info: 'FP.IEEE.Format.roundFinite_product_residual_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Format.roundFinite_product_residual_error

/-- info: 'FP.IEEE.Software.twoProduct_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoProduct_spec

/-- info: 'FP.IEEE.Software.finite_toRat_wordRat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.finite_toRat_wordRat

/-- info: 'FP.IEEE.Software.finite_of_toRat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.finite_of_toRat

/-- info: 'FP.IEEE.Software.binary_even_range_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_range_of_decode

/-- info: 'FP.IEEE.Software.binary_even_finite_of_real_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.binary_even_finite_of_real_range

/-- info: 'FP.IEEE.Software.twoProduct_bounded_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoProduct_bounded_of_finite

/-- info: 'FP.IEEE.Software.productResidual_isFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.productResidual_isFinite

/-- info: 'FP.IEEE.Software.TwoProductRange.residual_representable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.TwoProductRange.residual_representable

/-- info: 'FP.IEEE.Software.certifiedTwoProduct?_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoProduct?_of_range

/-- info: 'FP.IEEE.Software.certifiedTwoProduct?_success_iff_representable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.certifiedTwoProduct?_success_iff_representable

/-- info: 'FP.dot_compensation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_zero

/-- info: 'FP.dot_compensation_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_step

/-- info: 'FP.dot_compensation_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_finish

/-- info: 'FP.dot_compensation_defect_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_defect_bound

/-- info: 'FP.dot_compensation_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_input_bound

/-- info: 'FP.dot_compensation_relative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_relative_bound

/-- info: 'FP.dot_compensation_gamma_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.dot_compensation_gamma_bound

/-- info: 'FP.IEEE.Software.compensatedDotStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep_spec

/-- info: 'FP.IEEE.Software.compensatedDotCore_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotCore_spec

/-- info: 'FP.IEEE.Software.compensatedDot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_spec

/-- info: 'FP.IEEE.Software.compensatedDotStep_flags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep_flags_iff

/-- info: 'FP.IEEE.Software.compensatedDotCore_flags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotCore_flags_iff

/-- info: 'FP.IEEE.Software.compensatedDot_flags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_flags_iff

/-- info: 'FP.IEEE.Software.dot_compensation_initial_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.dot_compensation_initial_valid

/-- info: 'FP.IEEE.Software.compensatedDotStep?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedDotStep?_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep?_execution

/-- info: 'FP.IEEE.Software.compensatedDotStep?_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep?_valid

/-- info: 'FP.IEEE.Software.compensatedDotPass?_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotPass?_valid

/-- info: 'FP.IEEE.Software.compensatedDotPass?_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotPass?_execution

/-- info: 'FP.IEEE.Software.compensatedDot?_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_execution

/-- info: 'FP.IEEE.Software.compensatedDotPass?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotPass?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedDot?_success_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_success_iff_finite

/-- info: 'FP.IEEE.Software.compensatedDot?_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_complete

/-- info: 'FP.IEEE.Software.CompensatedDotPassFinite.result_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedDotPassFinite.result_finite

/-- info: 'FP.IEEE.Software.wordRat_cast_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordRat_cast_of_decode

/-- info: 'FP.IEEE.Software.wordDotSum_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDotSum_cast

/-- info: 'FP.IEEE.Software.wordDotAbsSum_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDotAbsSum_cast

/-- info: 'FP.IEEE.Software.compensatedDot?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_sound

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_of_finite

/-- info: 'FP.IEEE.Software.compensatedDot_gamma_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_gamma_of_finite

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_of_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_of_decoded

/-- info: 'FP.IEEE.Software.compensatedDot_gamma_of_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_gamma_of_decoded

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_backward

/-- info: 'FP.IEEE.Software.compensatedDot_error_radius_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_error_radius_of_finite

/-- info: 'FP.IEEE.Software.compensatedDot_exact_of_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_exact_of_zero_bound

/-- info: 'FP.IEEE.Software.compensatedDotEnclosure?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotEnclosure?_sound

/-- info: 'FP.IEEE.Software.compensatedDotEnclosure?_exists_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotEnclosure?_exists_of_finite

/-- info: 'FP.IEEE.Software.CompensatedDotStepRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedDotStepRange.toFinite

/-- info: 'FP.IEEE.Software.CompensatedDotPassRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedDotPassRange.toFinite

/-- info: 'FP.IEEE.Software.CompensatedDotRange.toFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.CompensatedDotRange.toFinite

/-- info: 'FP.IEEE.Software.compensatedDot?_complete_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_complete_of_range

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_of_range

/-- info: 'FP.IEEE.Software.compensatedDot_gamma_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_gamma_of_range

/-- info: 'FP.IEEE.Software.twoProduct_defect_zero_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.twoProduct_defect_zero_of_range

/-- info: 'FP.IEEE.Software.compensatedDotPass?_defect_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotPass?_defect_zero

/-- info: 'FP.IEEE.Software.compensatedDot?_defect_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot?_defect_zero

/-- info: 'FP.IEEE.Software.compensatedDot_exact_products_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_exact_products_bound

/-- info: 'FP.IEEE.Software.wordDotSum_pairList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDotSum_pairList

/-- info: 'FP.IEEE.Software.wordDotAbsSum_pairList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordDotAbsSum_pairList

/-- info: 'FP.IEEE.Software.compensatedDotList?_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotList?_complete

/-- info: 'FP.IEEE.Software.compensatedDotList_mixed_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotList_mixed_of_finite

/-- info: 'FP.IEEE.Software.compensatedDotList_exact_of_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotList_exact_of_zero_bound

/-- info: 'FP.Range.Interval.contains_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.Interval.contains_symmetric

/-- info: 'FP.Range.Interval.contains_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.Interval.contains_singleton

/-- info: 'FP.Range.roundErrorBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.roundErrorBound_sound

/-- info: 'FP.Range.interval_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.interval_range

/-- info: 'FP.Range.growthRat_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.growthRat_cast

/-- info: 'FP.Range.geomWeightRat_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.geomWeightRat_cast

/-- info: 'FP.Range.exactSumInterval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.exactSumInterval_sound

/-- info: 'FP.Range.exactDotInterval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.exactDotInterval_sound

/-- info: 'FP.Range.sumAccuracyBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.sumAccuracyBound_sound

/-- info: 'FP.Range.dotAccuracyBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.Range.dotAccuracyBound_sound

/-- info: 'FP.IEEE.Software.WordIn.of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.WordIn.of_decode

/-- info: 'FP.IEEE.Software.WordIn.decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.WordIn.decode

/-- info: 'FP.IEEE.Software.WordIn.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.WordIn.zero

/-- info: 'FP.IEEE.Software.add_zero_zero_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.add_zero_zero_decode

/-- info: 'FP.IEEE.Software.checkBinary_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkBinary_word_sound

/-- info: 'FP.IEEE.Software.checkAdd_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkAdd_word_sound

/-- info: 'FP.IEEE.Software.add_wordRat_roundFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.add_wordRat_roundFinite

/-- info: 'FP.IEEE.Software.checkTwoSum_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkTwoSum_word_sound

/-- info: 'FP.IEEE.Software.checkTwoProduct_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkTwoProduct_word_sound

/-- info: 'FP.IEEE.Software.StateIn.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.StateIn.zero

/-- info: 'FP.IEEE.Software.checkCompensatedStep_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedStep_word_sound

/-- info: 'FP.IEEE.Software.compensatedDotStep_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotStep_value

/-- info: 'FP.IEEE.Software.checkCompensatedDotStep_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedDotStep_word_sound

/-- info: 'FP.IEEE.Software.checkCompensatedFinish_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedFinish_word_sound

/-- info: 'FP.IEEE.Software.checkCompensatedPass_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedPass_word_sound

/-- info: 'FP.IEEE.Software.checkCompensatedSum_range_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedSum_range_sound

/-- info: 'FP.IEEE.Software.wordIn_sum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordIn_sum_bounds

/-- info: 'FP.IEEE.Software.checkCompensatedSum_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedSum_sound

/-- info: 'FP.IEEE.Software.compensatedSum_complete_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_complete_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedSum_enclosure_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_enclosure_of_range_certificate

/-- info: 'FP.IEEE.Software.checkCompensatedDotPass_word_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedDotPass_word_sound

/-- info: 'FP.IEEE.Software.checkCompensatedDot_range_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedDot_range_sound

/-- info: 'FP.IEEE.Software.wordIn_dot_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordIn_dot_bounds

/-- info: 'FP.IEEE.Software.checkCompensatedDot_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedDot_sound

/-- info: 'FP.IEEE.Software.compensatedDot_complete_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_complete_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedDot_enclosure_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_enclosure_of_range_certificate

/-- info: 'FP.IEEE.Software.wordIn_lists_of_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.wordIn_lists_of_decoded

/-- info: 'FP.IEEE.Software.compensatedSum_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedDot_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_of_range_certificate

/-- info: 'FP.IEEE.Software.pairedWordIn_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.pairedWordIn_getD

/-- info: 'FP.IEEE.Software.checkCompensatedDotList_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.checkCompensatedDotList_sound

/-- info: 'FP.IEEE.Software.compensatedDotList_complete_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDotList_complete_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedSum_mixed_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_mixed_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedSum_gamma_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedSum_gamma_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedDot_gamma_of_range_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_gamma_of_range_certificate

/-- info: 'FP.IEEE.Software.compensatedDot_mixed_backward_of_range_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FP.IEEE.Software.compensatedDot_mixed_backward_of_range_certificate
