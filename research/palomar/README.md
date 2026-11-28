# Palomar submission packages

Each entry has one statement, one proof import and one Comparator configuration. The statement consists of the definitions from the pinned `Statement.lean` and the theorem type in `entries.toml`. Only the generated challenge has a proof placeholder. The solution imports the original proof from an exact Git revision. Its axiom allowlist comes from that result’s checked contract. Multiple entries share the same proof dependency and Lake manifest.

## Prepare and verify

Use Python 3.11 or later. Choose a commit that contains the selected proofs. The generator writes a new directory. Run the checks on Linux with the pinned Lean release, `bwrap` and the bundled `nanoda_bin` on `PATH`. Comparator needs working user and network namespaces. The first command checks that the user running Comparator can create the sandbox.

```sh
bwrap --unshare-net --ro-bind / / true
python3 research/palomar/prepare.py HEAD /tmp/palomar-math
cd /tmp/palomar-math
export PATH="$(lean --print-prefix)/bin:$PATH"
lake exe cache get
lake build @math/ResearchLint:shared
for config in Palomar/*/comparator.json; do
  lake comparator --config "$config" || exit 1
done
```

The initial entries are the split-matroid pair (#40) and the sharp boundary-triangle bound (#81). The collection also includes packages for monochromatic subset sums (#59), the printed zig-zag condition (#64), dual pairs in flag complexes (#114), and the signed-set equality cases (#116). To prepare another entry, add its exact theorem type, mathematical scope, prior work and review record to `entries.toml`. The source statement must stand on its own using the registry's permitted imports. Review the generated challenge against the original publication before running Comparator.

For a registry submission, commit the generated files and the manifest to a public wrapper revision. Select `Palomar/<group>/comparator.json` and `Palomar/<group>/formalization.yaml` at that exact revision. The metadata identifies the separate, immutable substantive proof revision. The registry runs its own mechanical checks and editorial review. Registration requires the maintainer’s approval. [Palomar submission rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/5bd35cddcfc940532bb5f55e399d68b49b0986a5/CONTRIBUTING.md) · [Palomar verifier](https://github.com/PalomarRegistry/PalomarSubmission/tree/952cc3697b3f335c6cc0c21932e55ee92921dd35) · [Lean’s Comparator](https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Check.lean)
