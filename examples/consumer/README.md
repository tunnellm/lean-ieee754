# Downstream examples

This is a separate Lake package that depends on FP through `path = "../.."`.
It shares the parent checkout's dependency cache, but each example imports
public FP modules and has its own checked theorem.

From the FP checkout, run:

```sh
lake exe cache get
lake build FP FP.Verification fp
cd examples/consumer
lake build
```

| File | What it proves |
| --- | --- |
| [AbstractDot.lean](Examples/AbstractDot.lean) | The traditional componentwise backward bound for any rounding function satisfying the relative-error model. |
| [IEEEDot.lean](Examples/IEEEDot.lean) | A mixed forward bound for every five-term fp32 dot product with finite decoded operands in `[-1, 1]`; a kernel-checked interval certificate supplies the intermediate range conditions. |
| [CompensatedSum.lean](Examples/CompensatedSum.lean) | Every five-term fp64 compensated sum with finite decoded operands in `[-1, 1]` has absolute error less than `10⁻¹²`, including inputs subject to gradual underflow. |

All examples use nearest-even where IEEE arithmetic is involved. The dot
example uses separate multiply/add operations; the compensated-sum example
uses the library's specific TwoSum schedule. The proofs do not assume that a
hardware implementation executes either schedule.

For a new directory, follow [Using FP](../../docs/Using.md). Adjust the FP path
and omit `packagesDir` if the new project should have its own dependency cache.
