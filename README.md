# Mathematical conjectures

Proofs, counterexamples, and research notes on published mathematical conjectures.
Ali Romman created and maintains the project. OpenAI Codex assisted with searches,
mathematical arguments, and Lean formalizations. Each research note documents its sources.

## Discoveries

The catalogue includes work in draft pull requests. Proof links point to fixed revisions.

1. **Restricted $U$-polynomials of trees.** Two nonisomorphic 32-vertex trees have the same restricted polynomial through five edge cuts. The predicted minimum was 34. The proposed formula fails at every cut depth $m \ge 5$, and the minimum is at most $3(m+1)^2$ for every $m \ge 1$. [Argument][u-note] · [Lean bound][u-bound] · [Lean refutation][u-proof] · [PR #7][pr7]

2. **Average size of a maximal matching.** Among trees on 15 vertices with diameter 11, moving one leaf raises the mean size of a maximal matching from $6$ to $259/43$. This disproves the proposed maximum of Engbers and Erey. [Argument][matching-note] · [Lean proof][matching-proof] · [PR #1][pr1]

3. **Liu’s three conjectures on Walker’s triangle inequality.** All three inequalities hold for acute and right triangles. Each weight in Liu’s cyclic sum has a corresponding range of real exponents, where $a,b,c$ are the side lengths.

   - $a^k$ for $k \le 4$. [Lean proof][liu1] · [PR #2][pr2]
   - $(b+c)^k$ for $k \ge -10$. [Lean proof][liu2] · [PR #3][pr3]
   - $(b+c-a)^k$ for $k \ge -3$. [Lean proof][liu3] · [PR #4][pr4]

**Research note.** Stanley’s question asks whether the chromatic symmetric function distinguishes all trees. A two-site branch exchange cannot yield a counterexample. A separate search distinguished 111,144 trees in a three-site family. The general question remains open. [Argument][stanley-note] · [Search code][stanley-code] · [PR #6][pr6]

## Reproduce a result

From a local clone, check out the result’s pull request (for example, `gh pr checkout 7`).
Each note gives its reproduction commands. For the Lean proofs, Elan selects the
pinned toolchain and Lake reads the exact Mathlib revision from the manifest. [Install Elan][elan]

[Citation](CITATION.cff) · [Apache License 2.0](LICENSE)

[u-note]: https://github.com/aliromman/math/blob/ffd3c2db319516682a86165833684f6b7def50f1/conjectures/RestrictedUMinimum/README.md
[u-bound]: https://github.com/aliromman/math/blob/ffd3c2db319516682a86165833684f6b7def50f1/conjectures/RestrictedUMinimum/Growth.lean#L159
[u-proof]: https://github.com/aliromman/math/blob/ffd3c2db319516682a86165833684f6b7def50f1/conjectures/RestrictedUMinimum/Threshold.lean#L82
[pr7]: https://github.com/aliromman/math/pull/7
[matching-note]: https://github.com/aliromman/math/blob/d9c0d8fcbbefa8eaa4de48f137a8d00d3ff47081/conjectures/EngbersErey/README.md
[matching-proof]: https://github.com/aliromman/math/blob/d9c0d8fcbbefa8eaa4de48f137a8d00d3ff47081/conjectures/EngbersErey/Solution.lean#L73
[pr1]: https://github.com/aliromman/math/pull/1
[liu1]: https://github.com/aliromman/math/blob/49d11be30e532489f13c49acd25daffbf0c1f8d2/conjectures/LiuWalkerOne/Solution.lean
[pr2]: https://github.com/aliromman/math/pull/2
[liu2]: https://github.com/aliromman/math/blob/3ea47dfea9d88011674a698dcaa63e8c0faa9e60/conjectures/LiuWalkerTwo/Solution.lean
[pr3]: https://github.com/aliromman/math/pull/3
[liu3]: https://github.com/aliromman/math/blob/bb74f289fdddc5874f9adbd2376b1393ed826572/conjectures/LiuWalkerThree/Solution.lean
[pr4]: https://github.com/aliromman/math/pull/4
[stanley-note]: https://github.com/aliromman/math/blob/50c653f08a97c823ee0cd621eeb600d04a518dd0/conjectures/StanleyTreeCSF/README.md
[stanley-code]: https://github.com/aliromman/math/blob/50c653f08a97c823ee0cd621eeb600d04a518dd0/conjectures/StanleyTreeCSF/replay.py
[pr6]: https://github.com/aliromman/math/pull/6
[elan]: https://github.com/leanprover/elan
