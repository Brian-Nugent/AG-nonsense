# AG-nonsense

A shared Lean 4 workspace for algebraic geometry, with the goal of contributing results to
[mathlib](https://github.com/leanprover-community/mathlib4).

This is a standalone project that depends on mathlib. Lean and mathlib are pinned, and
`lake-manifest.json` records the complete dependency versions for reproducible builds.

## Getting started

Install Lean through Elan and the Lean 4 extension for VS Code, then run:

```sh
git clone https://github.com/Brian-Nugent/AG-nonsense.git
cd AG-nonsense
lake exe cache get
lake build
```

Elan uses `lean-toolchain` to select the required Lean version. The cache command downloads
mathlib's compiled files so you do not need to compile mathlib from scratch.
Open this directory in VS Code and start with `AGNonsense/Basic.lean`.

## Working together

- Put proofs in `AGNonsense/`, using focused files as the project grows.
- Import new files from `AGNonsense.lean` so the default build checks them.
- Use a branch for each topic and open pull requests into this repository's `main` branch.
- Run `lake build` before pushing. GitHub Actions also checks pushes and pull requests.
- Do not edit `.lake/packages/mathlib`; Lake manages that dependency directory.

`AGNonsense/Basic.lean` contains a small example using the category of schemes to check
the setup. Replace or extend it with the results you want to prove.

## Contributing results to mathlib

Use mathlib's existing namespaces and style where appropriate. When a result is ready,
move it into the relevant `Mathlib/` file in your mathlib fork, check it against mathlib's
current version, and open a pull request to `leanprover-community/mathlib4`.
The Apache 2.0 license matches mathlib's license.

## Updating mathlib

Choose a mathlib commit and put its full commit hash in `lakefile.toml`. Copy the
`lean-toolchain` value from that same mathlib commit into this project's `lean-toolchain`,
then run:

```sh
lake update mathlib
lake exe cache get
lake build
```

Commit `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json` together so everyone
gets the same versions. Check that your proofs still build before merging the update.
