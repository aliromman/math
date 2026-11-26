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
  Combine exact computation and mathematical arguments. Use independent
  researchers when they can make progress on distinct approaches.
- Start with one conjecture. Change targets when further work has poor prospects.
  Seek additional discoveries within the available budget.
- Reduce witnesses when possible. Keep a research ledger with the source,
  approach, outcome, useful failed attempts, and exact search bounds.
  Report elapsed time and token use when measured. Display time to the
  nearest minute and tokens to the nearest 10,000. Count each participant's
  work once. Identify cached input and include reasoning in output.
  Keep raw transcripts and large search outputs out of version control.

## Verification

- Give the exact conjecture its own Lean statement. Preserve every hypothesis,
  quantifier, convention, and uniqueness condition in the source.
- Prove that statement or its negation in a separate module. Give a
  mathematical argument that a reader can check independently.
- Use the latest stable Lean release and compatible Mathlib release. Pin
  the toolchain and dependencies. Build from a clean checkout. Run
  `python3 scripts/verify.py` to replay every research module in the kernel
  and check each result's exact transitive axioms.
- Exclude proof placeholders, circular arguments, and unjustified axioms.
  Have an independent agent challenge the mathematical argument and its
  translation into Lean. Resolve findings and repeat verification after
  substantive changes.
- State the limits of computations and partial results. Claim a solution
  only after the proof, independent audit, and CI checks pass.

## Publication

- Preserve the scaffold commit on `main`. Start one branch from `main` and
  one draft pull request per conjecture. Add later work to the same pull
  request. Leave merging to the maintainer or an explicitly authorized reviewer.
- Keep the original source reference, statement, argument, and formal proof
  together under `conjectures/`. Share definitions and lemmas when several
  results use them. Document the significance, prior-art search, reproduction
  commands, and role of AI.
- Lead the pull request with the finding or the open obstacle. Credit prior
  work. Update the README catalogue with links to the note, proof, and pull
  request. Identify partial results and extensions of known work.
- Review the diff and its author and committer metadata before pushing.
  Exclude credentials, private contact details, machine paths, and raw logs.
  Add infrastructure only when the research or its verification requires it.
