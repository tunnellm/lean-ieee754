# FP repository guidance

This is a Lean 4 floating-point numerical-analysis library. Start with
`docs/Using.md` for the theorem map, `README.md` for detailed statements, and
`IEEE754Coverage.md` for the precise IEEE scope and remaining obligations.

Use the pinned Lean/mathlib versions. Search existing declarations before
introducing models or lemmas; use Lean MCP when available to inspect types,
goals, diagnostics, and axiom dependencies.

Keep format, rounding mode, evaluation schedule, and finite/range conditions
explicit. Retain underflow terms and gamma-bound size hypotheses. A failed
interval certificate is not proof of overflow. Full IEEE conformance and
hardware/compiler correctness are not established by this project.

Do not add proof placeholders, project axioms, or native evaluation proof
oracles. Follow `CONTRIBUTING.md` for regression examples and axiom guards.
Keep `import FP` free of test/audit imports. Validate changes with
`lake build FP FP.Verification fp`; when changing public imports, APIs, or
packaging, also run `lake build` in `examples/consumer`.
