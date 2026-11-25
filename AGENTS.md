# Research instructions

Seek original proofs or counterexamples to published mathematical conjectures.
Prefer short arguments that explain why a conjecture holds or fails.

## Research

- Choose open conjectures for their mathematical significance and a concrete
  route to a proof or counterexample. Seek ambitious results in any field.
  Prefer a short argument or a surprising example that explains the answer.
- Spend most of the research effort on mathematics. Use the techniques that
  best fit each problem. Revisit earlier pull requests or infrastructure only
  when the task or verification requires it.
- Select an identifiable academic source. Read its definitions, scope, and
  hypotheses. Check for earlier solutions. Keep screening short. Spend most of the
  budget deriving proofs, searching for witnesses, and testing the argument.
- Pursue an approach while it gives new constraints, examples, or lemmas.
  Change course when a specific obstacle defeats it. Use other agents for
  distinct mathematical tasks.
- Reduce counterexamples when possible. Keep a short note for each serious
  attempt with the source, approach, outcome, and any reusable insight.
  Give exact search bounds and elapsed time or compute use when available.
  Use these notes to select future problems and methods. Keep large outputs
  in the ignored scratch directory.

## Verification

- Give the exact conjecture its own Lean statement. Preserve every hypothesis,
  quantifier, convention, and uniqueness condition in the source.
- Prove that statement or its negation in a separate module. Include a
  mathematical argument that a reader can check independently.
- Verify each result with the latest stable Lean release and the latest
  compatible Mathlib release. Pin the toolchain and dependency revisions.
- Build from a clean checkout. Check the final theorem's dependencies and
  transitive axioms. Exclude proof placeholders, circular arguments, and
  unjustified axioms. Include a machine-checked axiom expectation with the proof.
- Have an independent agent try to invalidate the argument and its translation
  into Lean. Resolve findings. Simplify the proof, dependencies, and build
  where possible. Repeat verification after substantive changes.
- Report numerical evidence and partial results with their scope. Claim a
  solution only after the proof, independent audit, and CI checks pass.

## Publication

- Keep the initial scaffold in one commit on `main`. Start a separate branch
  from `main` for each conjecture and use one draft pull request per conjecture.
  Add subsequent work to that pull request. Leave merging to the maintainer.
- Keep the source, statement, argument, and formal proof in a single directory
  under `conjectures/`. Document the result's significance, prior-art search,
  reproduction commands, and the role of AI.
- Lead each pull request with the discovery or the open mathematical obstacle.
  State the original question, what the result changes, and why the proof
  works in terms a reader can follow without Lean. Use a displayed equation,
  a small example, or a diagram when it clarifies the argument. Give exact
  verification commands and identify the contribution of prior work and AI.
- Treat commits, draft pull requests, and their history as public. Review each
  diff and its author metadata before pushing. Exclude credentials, personal
  details, private files, machine paths, and raw logs.
- Keep the README factual. Add infrastructure only when the research or its
  verification requires it.
