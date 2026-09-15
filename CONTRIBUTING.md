# Contributing

The project uses [Apache-2.0](LICENSE). Contributions should use the same license;
attribute any adapted material and retain required notices.

Use the checked-in `lean-toolchain` and dependency revisions. Build with:

```sh
lake exe cache get
lake build FP FP.Verification fp
cd examples/consumer
lake build
```

`FP.lean` is the public aggregate. Keep tests and diagnostic commands out of
its import closure. Add regression examples to the appropriate `*Tests.lean`
or boundary module, and ensure they are imported by `FP.Verification`.
When adding a public module, make it reachable from `FP.lean` and describe its
main entry points in the documentation.

Proofs must contain no `sorry`, `admit`, project axioms, or `native_decide`.
Use kernel reduction (`decide +kernel`) for closed numerical certificates.
Add axiom regression guards for significant new results, following
`FP/Verification.lean`; the accepted standard axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

State evaluation order, rounding mode, format, and exceptional behavior in the
definition or theorem being proved. Preserve the distinction between a total
result/flag theorem and a numerical accuracy theorem with finite/range
hypotheses. Record IEEE coverage changes in `IEEE754Coverage.md`, including
anything still requiring correspondence review against the written standard.

For a proposed theorem, explain the intended mathematical statement and which
existing result it extends. Include boundary cases appropriate to the change,
such as zero-length inputs, signed zero, subnormals, cancellation, and overflow.
Attribute adapted proofs and respect the source's license. Keep dependency
migrations separate from numerical theorem changes when practical.
