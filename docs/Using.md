# Using FP in another project

FP is a Lake dependency. Its proofs become available through Lean imports;
the source files and this guide help people and agents find the right theorem.
Use the exact toolchain from `lean-toolchain` (currently Lean 4.33.1).

## A local project

For sibling directories `FP/` and `Krylov/`, put this in `Krylov/lakefile.toml`:

```toml
name = "Krylov"
version = "0.1.0"
defaultTargets = ["Krylov"]

[[require]]
name = "FP"
path = "../FP"

[[lean_lib]]
name = "Krylov"
```

Copy `FP/lean-toolchain` to `Krylov/lean-toolchain`, create `Krylov/Krylov.lean`,
and put `import FP` in it. In `Krylov/`, run:

```sh
lake update
lake exe cache get
lake build
```

Commit the resulting `lake-manifest.json`. Keep FP's mathlib revision when
adding dependencies; changing it is a toolchain/dependency migration that
requires rebuilding the proofs.

For a published copy, replace the local `path` with `git` and `rev` fields:

```toml
[[require]]
name = "FP"
git = "https://github.com/tunnellm/lean-ieee754.git"
rev = "v0.1.0"
```

This selects release `v0.1.0`. Commit the manifest produced by `lake update`
to retain the resolved commit and dependency revisions. To adopt another
version, use a published release tag or a full commit hash. The current
development commit can be read with:

```sh
git ls-remote https://github.com/tunnellm/lean-ieee754.git refs/heads/main
```

Update the selected revision when adopting a reviewed newer version. Lake's
[dependency documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
explains both forms.

## Find the theorem you need

Names below are fully qualified. Importing the indicated module is sufficient.
Use `#check` or Lean's hover information for the exact hypotheses and result.

| Task | Import | Entry point |
| --- | --- | --- |
| Traditional dot-product backward stability | `FP.InnerProduct` | `FP.traditional_innerProduct_backward` |
| Forward error from a mixed backward bound | `FP.MixedBackward` | `FP.MixedBackwardStable.forward` |
| Sequential or pairwise summation | `FP.IEEE.Software.TotalReductionBounds` | `FP.IEEE.Software.sequentialSum_mixed_of_certificate`, `FP.IEEE.Software.pairwiseSum_mixed_of_certificate` |
| IEEE dot-product accuracy with a range certificate | `FP.IEEE.Software.TotalReductionBounds` | `FP.IEEE.Software.dot_mixed_of_certificate` |
| Compensated summation accuracy | `FP.IEEE.Software.CompensatedRangeCorollaries` | `FP.IEEE.Software.compensatedSum_of_range_certificate` |
| Compensated dot-product accuracy | `FP.IEEE.Software.CompensatedRangeCorollaries` | `FP.IEEE.Software.compensatedDot_of_range_certificate` |
| Division error | `FP.IEEE.Software.Division` | `FP.IEEE.Software.mixedDiv_even_mixed_error` |
| Square-root error | `FP.IEEE.Software.Sqrt` | `FP.IEEE.Software.mixedSqrt_even_mixed_error` |
| Outward-rounded finite intervals | `FP.IEEE.Software.Intervals` | `FP.IEEE.Software.enclose_sound` |

The [downstream example package](../examples/consumer/README.md) demonstrates
actual theorem applications, including proofs for every input in a domain.

## Give a new agent this context

Place the following in the consuming project's `AGENTS.md`, adjusting the
dependency path for a local checkout or `.lake/packages/FP` for a Git dependency:

```markdown
This project uses the FP Lean library for floating-point error analysis.
Its source is at ../FP. Read ../FP/docs/Using.md, ../FP/README.md, and
../FP/IEEE754Coverage.md before adding floating-point models or error lemmas.
Search existing declarations and check their types in Lean; reuse the library
through imports. Use Lean MCP when available to check theorem applications.

Keep the chosen format, rounding mode, evaluation order, and algorithm explicit.
Discharge finite/range hypotheses or use the executable interval certificates.
Preserve underflow terms and any gamma-bound size assumptions. A failed range
certificate does not establish that the computation overflows.

Do not add sorry, admit, custom axioms, or native_decide to establish results.
State any remaining algorithm assumptions explicitly. Check the resulting
theorems and their axiom dependencies. Run lake build in this project.
```

## A starting point for Krylov methods

First describe the mathematical algorithm and its precise floating-point
evaluation schedule. Represent Euclidean vectors with a type whose norm has
the intended meaning, such as `EuclideanSpace ℝ (Fin n)`. Establish adapters
between that representation and FP's indexed reductions.

Then assemble row-wise dot-product bounds into a matrix-vector bound, combine
the scalar addition/multiplication lemmas into an `axpy` bound, and use division
and square-root lemmas for normalization. Orthogonalization and Arnoldi/Lanczos
relations can build on those components. These vector and Krylov theorems are
future work; importing FP supplies their scalar numerical foundations.

For proofs that permit gradual underflow, use mixed absolute/relative bounds.
Pure relative results have stronger hypotheses. Theorems about FP's reference
software or Lean's native logical model do not by themselves verify a BLAS
implementation, compiler optimization, or hardware execution.
