# Releasing FP

GitHub hosts the development repository and tagged releases. Zenodo can archive
selected releases as citable software records with DOIs. An archive preserves
the source snapshot; checking the proofs still requires the pinned toolchain
and dependencies.

## First publication

The repository is `tunnellm/lean-ieee754`, licensed under Apache-2.0, with
Marc A. Tunnell as the citation author. Review [CITATION.cff](../CITATION.cff)
before each release and keep its version synchronized with `lakefile.toml`
and the release tag. Add the actual release date when publishing; add a DOI
only once it has been assigned. Zenodo account setup and archiving are managed
by the repository owner.

Use a single `CITATION.cff` as citation metadata. Both GitHub and Zenodo support
it; if `.zenodo.json` is also present, Zenodo takes that file's metadata instead.
See [GitHub citation files](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
and [Zenodo metadata](https://help.zenodo.org/docs/github/describe-software/).

Validate the completed file with
[`cffconvert`](https://github.com/citation-file-format/cffconvert):

```sh
cffconvert --validate -i CITATION.cff
```

Push the checked local source and update `docs/Using.md` when recommending a
new revision. Release archives contain the source and pinned dependency
manifests; `.lake/` and dependency checkouts are excluded from version control.

## Validate the release candidate

Run the checks used by CI:

```sh
lake exe cache get
lake build FP FP.Verification fp
cd examples/consumer
lake build
```

Check that GitHub CI succeeds on the exact release commit. Review the coverage
ledger and release notes against what is proved. The release description must
retain the finite/range, rounding-mode, written-standard, and native/hardware
qualifications. Record the toolchain and pinned mathlib revision in the release
notes. Complete the citation author/license fields before publishing a DOI.

## Optional Zenodo archive

Before publishing the GitHub release to archive:

1. Sign into Zenodo and connect the GitHub account.
2. In Zenodo's GitHub settings, synchronize repositories and enable FP's
   repository. This enables automatic archiving of subsequent releases.
3. On GitHub, publish a release based on the checked version tag (initially
   `v0.1.0`) with the corresponding changelog entry and citation metadata.
4. Wait for ingestion, then inspect the Zenodo record: authors, title, license,
   version, and source archive must be correct.
5. Add the actual DOI link to the repository documentation and citation
   metadata as appropriate. Distinguish the version DOI, which identifies
   the archived snapshot, from the concept DOI for the evolving project; see
   [Zenodo DOI versioning](https://support.zenodo.org/help/en-gb/1-upload-deposit/97-what-is-doi-versioning).

For the first archive, add its version DOI to the top-level `doi` field in
`CITATION.cff`, paired with that record's `version` and `date-released`. Replace
the pending Zenodo link in the README and the `CITATION.cff` message with the
concept DOI, using "To cite the version of the proofs you used, see [Zenodo]"
with the actual link. Replace the README's placeholder badge with a DOI badge
linked to the concept DOI, which resolves to the latest archived version and
provides access to earlier versions.
The top-level `doi` identifies the archived version, even if the link is added
to `main` after that version was published. Do not move the release tag to add
the link.

With GitHub integration, the DOI normally becomes available after the release
is published and ingested. For a manual upload, Zenodo also supports
[reserving a DOI before publication](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/).
Use the chosen archive workflow consistently so the release has one software
record rather than separate manual and automatic uploads.

An existing tag alone does not trigger a new archived release. If a GitHub
release was published before integration was enabled, follow Zenodo's manual
upload procedure or archive a subsequent release; do not silently move a
published tag. Do not publish a new version solely to add a DOI badge.

The account connection is performed by its owner; no Zenodo credentials or
tokens belong in this repository. The procedure is documented in
[enabling a repository](https://help.zenodo.org/docs/github/enable-repository/),
[archiving a release](https://help.zenodo.org/docs/github/archive-software/github-upload/),
and [manual software upload](https://help.zenodo.org/docs/github/archive-software/).
