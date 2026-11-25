# Research instructions

Seek original proofs or counterexamples to published mathematical conjectures.
Prefer short arguments that explain why a conjecture holds or fails.

## Research

- Select a conjecture from an identifiable academic source. Read its definitions,
  scope, and hypotheses. Check the literature for earlier solutions.
- Consider any field. Give priority to tractable problems in graph theory,
  combinatorics, and polynomial inequalities. Look for overlooked structure
  and questions with little computational exploration.
- Keep screening brief. Spend most of the research budget on solving.
  Combine exact computation and mathematical arguments. Use parallel
  researchers when they can make independent progress.
- Start with one conjecture. Change targets when further work has poor prospects.
  Seek additional discoveries within the available budget.
- Prefer simple counterexamples. Reduce a witness when possible. Record
  useful failed approaches and their limits in the draft or in local notes.
  Keep large search outputs in the ignored scratch directory.

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
- Treat commits, draft pull requests, and their history as public. Review each
  diff and its author metadata before pushing. Exclude credentials, personal
  details, private files, machine paths, and raw logs.
- Keep the README factual. Add infrastructure only when the research or its
  verification requires it.
