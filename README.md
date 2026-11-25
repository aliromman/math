# Mathematical conjectures

This repository studies published mathematical conjectures in Lean 4.
Each directory under `conjectures/` contains a source citation, the
conjecture statement, and the results of the investigation.

## Verification

Install [Elan](https://github.com/leanprover/elan), then run the following
command from the repository root.

```sh
lake build
```

Elan reads the Lean version from `lean-toolchain`. Lake reads the exact
Mathlib revision and its dependencies from `lake-manifest.json`.
Each solution names its main theorem and gives the command to check its axioms.
