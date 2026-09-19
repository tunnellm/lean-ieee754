# FP: IEEE 754 and numerical analysis in Lean

FP is a Lean 4 library for proving error bounds for floating-point computations.
It connects explicit IEEE binary32/binary64 arithmetic to real-number statements
about rounding error, summation, and dot products.

> **Development provenance:** This library’s code, proofs, and documentation were
> written primarily by large language models under human direction. Lean checks
> the formal proofs against their stated definitions and assumptions. The
> formalization’s correspondence to IEEE 754 and its numerical-analysis claims
> has not yet undergone independent expert review.

The intended workflow is to compose existing numerical bounds into a proof of
your algorithm. The [usage guide](docs/Using.md) maps common tasks to theorems.

## What is available

- Scalar arithmetic: addition, subtraction, multiplication, division, FMA,
  square root, and binary32/binary64 conversion, with result and exception proofs.
- Sequential and pairwise sums, dot products, and their error bounds.
- TwoSum, TwoProduct, compensated summation, and compensated dot products.
- Bounds that account for gradual underflow, plus traditional relative-error
  results under stronger range conditions.
- Executable range and accuracy certificates, with proofs of their soundness.

There are complete downstream examples for an
[abstract dot product](examples/consumer/Examples/AbstractDot.lean), an
[IEEE fp32 dot product](examples/consumer/Examples/IEEEDot.lean), and
[fp64 compensated summation](examples/consumer/Examples/CompensatedSum.lean).

## Use FP in a Lean project

Use Lean **4.33.1** and add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "FP"
git = "https://github.com/tunnellm/lean-ieee754.git"
rev = "v0.1.0"
```

Import the public toolkit with:

```lean
import FP
```

Follow [Using FP](docs/Using.md) for setup, pinned dependencies, the theorem map,
and instructions for a proof-writing agent. Commit your `lake-manifest.json`
to retain the resolved revisions.

## Build this repository

With the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build FP FP.Verification fp
```

This checks the library, regression examples, and principal-theorem axiom guards.
`import FP` exposes the public toolkit without importing those tests or guards.
CI also builds the separate [example package](examples/consumer/README.md).

## Scope and status

The current release proves arithmetic implementations against formal
binary32/binary64 contracts. Complete coverage of the declared IEEE 754-2019
scope and independent review of its correspondence to the written standard
remain open. See the [coverage ledger](IEEE754Coverage.md).

Numerical bounds retain their stated rounding mode, evaluation order, and
input/range hypotheses. Nearest-even is the current focus for reduction bounds.
A rejected range certificate does not establish that the computation overflows.

## Reference and development

Read the reference for the part you are using:

- [IEEE arithmetic](docs/Arithmetic.md): rounding, operations, conversions,
  intervals, neighbors, and scaling.
- [Summation and dot products](docs/Reductions.md): schedules, error bounds,
  and range certificates.
- [Compensated arithmetic](docs/Compensated.md): TwoSum, TwoProduct, and
  compensated reductions.
- [Error models and proof foundations](docs/Foundations.md): relative and mixed
  errors, IEEE hypotheses, and optional native bridges.

For development, see [Contributing](CONTRIBUTING.md) and the
[Changelog](CHANGELOG.md).

## License and citation

FP is licensed under [Apache-2.0](LICENSE). Dependencies retain their own licenses.

To cite the version of the proofs you used, see [Zenodo](https://doi.org/10.5281/zenodo.22775703).

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22775703.svg)](https://doi.org/10.5281/zenodo.22775703)
