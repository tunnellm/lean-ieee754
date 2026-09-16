# Changelog

## 0.1.0 — 2026-09-15

Initial research release of the FP numerical-analysis toolkit for Lean 4.33.1.
The mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`; transitive
dependency revisions are recorded in `lake-manifest.json`.

- Traditional relative and mixed-error models, with backward/forward bounds
  for dot products and sequential/pairwise summation.
- Explicit binary32/binary64 interchange representations and executable
  integer/rational reference arithmetic, with formal result/flag refinement
  for add, subtract, multiply, divide, FMA, and square root.
- Gradual-underflow-aware nearest-even numerical bounds and rational interval
  certificates that discharge intermediate range conditions.
- TwoSum and TwoProduct results, compensated summation and Dot2 analysis,
  and domain certificates for compensated accuracy and enclosures.
- Optional finite/nonoverflow bridges to Lean's native floating-point logical
  model, principal-theorem axiom guards, and kernel-checked boundary examples.
- A public import aggregate, downstream examples, and reuse/contribution guides.

The project does not assert full IEEE 754 conformance. Remaining operations,
written-standard correspondence review, and optional native bridges are listed
in [IEEE754Coverage.md](IEEE754Coverage.md). The API may change before 1.0;
pin a release commit for reproducible downstream proofs.
