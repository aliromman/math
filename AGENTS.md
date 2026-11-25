# Research instructions

Seek original proofs or counterexamples to published conjectures. Prefer short
arguments that explain why a conjecture holds or fails.

## Research

- Across investigations, spend about 75% of research time on well-known, difficult
  conjectures and 25% on established questions with meaningful consequences or
  research interest. Favor longstanding problems in these groups. Consider any
  field, especially Erdős problems, integer equations, graph theory, combinatorics,
  and polynomial inequalities.
- Read the academic source. Check its definitions, scope, and hypotheses, and
  search for earlier solutions. Keep screening brief. Spend most of the budget
  on new arguments, constructions, and exact computation.
- Pursue one main question at a time. Divide independent approaches among
  researchers. Continue while an approach yields examples or lemmas. Change
  course when a specific obstacle blocks progress. Reduce counterexamples when
  possible and seek further discoveries within the budget.
- Record each serious attempt’s source, significance, approach, outcome, and
  reusable insights. Give exact search bounds and time or compute used when
  available. Use these notes to guide later work. Keep bulk output in `scratch/`.

## Verification

- State the exact conjecture in its own Lean module. Preserve every hypothesis,
  quantifier, convention, and uniqueness condition. Prove it or its negation in
  a separate module. Give an argument a reader can check independently of Lean.
- Use the latest stable Lean release and latest compatible Mathlib release. Pin
  the toolchain and dependency revisions. Build from a clean checkout and replay
  the proof in the kernel. Inspect the final theorem’s dependencies and enforce
  its expected transitive axiom list in Lean. Exclude placeholders, circular
  arguments, and unjustified axioms.
- Have an independent agent challenge the argument and its Lean translation.
  Resolve findings, simplify the proof, dependencies, and build where possible,
  and rerun checks after substantive edits. State the limits of numerical and
  partial results. Claim a solution only after the proof, independent audit, and CI pass.

## Publication

- Preserve the scaffold commit on `main`. Use one branch from `main` and one
  draft pull request per conjecture. Add later work to the same pull request.
  Only the maintainer merges.
- Keep each conjecture’s source, statement, argument, and proof in one directory
  under `conjectures/`. Lead the pull request with the discovery or open obstacle.
  Explain its significance and the argument without Lean terminology. Include the
  prior-art search and reproduction commands. Credit prior work and state the role of AI.
- Check each diff and its author and committer metadata before pushing. Exclude
  credentials, private files, personal contact details, machine paths, and raw logs.
- Rank discoveries by significance in the README. Link each proof and pull request
  and label partial results. Add infrastructure only when research or verification requires it.
