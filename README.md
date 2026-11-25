# Mathematical conjectures

Proofs, counterexamples, and research notes on published mathematical conjectures.
Ali Romman created and maintains the project. OpenAI Codex assisted with searches,
mathematical arguments, and Lean formalizations. Each research note documents its sources.

## Discoveries

Proof links point to fixed revisions. Each pull request tracks the research draft and its review. [Latest pull requests][pulls]

1. **Restricted $U$-polynomials of trees.** Two nonisomorphic 32-vertex trees have the same restricted polynomial through five edge cuts. The predicted minimum was 34. The proposed formula fails at every cut depth $m \ge 5$, and the minimum is at most $3(m+1)^2$ for every $m \ge 1$. [Argument][u-note] · [Lean bound][u-bound] · [Lean refutation][u-proof] · [PR #7][pr7]

2. **Packing patterns in words.** Burstein, Hästö, and Mansour asked which words maximize the number of occurrences of given patterns.

   - For the pattern $12\!-\!1$ (an adjacent rise followed later by a repeat of its first letter), the exact maximum at length $n$ is $\lfloor n(n-1)/6\rfloor$. Two letters attain it for every $n$, giving packing density $1/3$. [Lean proof][packing] · [PR #13][pr13]
   - The word `111342222` packs 61 copies of the three layered patterns `11123`, `13222`, and `11322` in total. Every layered word of the same length on the same alphabet has at most 60. [Lean proof][layered] · [PR #17][pr17]

3. **Roots of graph degree polynomials.** Write $D_G(x)=\sum_{v}x^{\deg(v)}$.

   - For coprime positive integers $p,q$, some simple graph on $n\ge1$ vertices has root $-p/q$ exactly when $p+q$ divides $n$ for odd $n$, or $2(p+q)$ divides $n$ for even $n$. [Lean proof][rational-roots] · [PR #12][pr12]
   - Every nonreal root of a finite tree’s degree polynomial has modulus greater than one. This extends George’s open-disk prediction to the boundary. [Lean proof][tree-roots] · [PR #10][pr10]

4. **Sun’s circular ordering conjectures.** Two obstructions describe when adjacent pairs must repeat a value.

   - In a finite abelian group of odd order $N\ge5$, removing any two elements leaves a set with no circular ordering whose directed differences are all distinct. [Lean proof][group-cycles] · [PR #18][pr18]
   - Four distinct positive numbers force a repeated directed difference or adjacent product in every circular order exactly when the middle two are the harmonic and arithmetic means of the extremes. One example is $2,3,4,6$. [Lean proof][real-cycles] · [PR #19][pr19]

5. **Average size of a maximal matching.** Among trees on 15 vertices with diameter 11, moving one leaf raises the mean size of a maximal matching from $6$ to $259/43$. This disproves the proposed maximum of Engbers and Erey. [Argument][matching-note] · [Lean proof][matching-proof] · [PR #1][pr1]

6. **Liu’s three conjectures on Walker’s triangle inequality.** All three inequalities hold for acute and right triangles. Each weight in Liu’s cyclic sum has a corresponding range of real exponents, where $a,b,c$ are the side lengths.

   - $a^k$ for $k \le 4$. [Lean proof][liu1] · [PR #2][pr2]
   - $(b+c)^k$ for $k \ge -10$. [Lean proof][liu2] · [PR #3][pr3]
   - $(b+c-a)^k$ for $k \ge -3$. [Lean proof][liu3] · [PR #4][pr4]

7. **Prime powers and Lucas sequences.** Two numerical examples settle conjectured bounds of Sun.

   - The first nine primes at exponent $1/2000$ violate the proposed real-power extension of Mandl’s inequality. [Lean proof][prime-powers] · [PR #16][pr16]
   - For the Lucas sequence with $u_0=0$, $u_1=1$, and $u_{n+2}=3u_{n+1}+26u_n$, the ratio $u_{n+1}^{1/(n+1)}/u_n^{1/n}$ increases from $n=5$ to $n=6$. [Lean proof][lucas] · [PR #11][pr11]

8. **Liu’s refinements of the Erdős–Mordell inequality.** An isosceles triangle violates the proposed weighted upper bound at $k=3999/1000$. A thin obtuse triangle violates a separate proposed lower bound involving its medians. [Weighted bound proof][weighted] · [PR #14][pr14] · [Median bound proof][median] · [PR #15][pr15]

## Partial results

- **Convex heptagons.** A finite SAT search rules out a heptagon-free 33-point extension of one specific 27-point pattern of triple orientations from the classical Erdős–Szekeres construction. The general 33-point question remains open. [Argument][heptagon-note] · [Search code][heptagon-search] · [PR #9][pr9]
- **Stanley’s tree question.** A two-site branch exchange cannot produce nonisomorphic trees with the same chromatic symmetric function. A separate search distinguished 111,144 trees in a three-site family. The general question remains open. [Argument][stanley-note] · [Search code][stanley-code] · [PR #6][pr6]

## Reproduce a result

From a local clone, check out the result’s pull request (for example, `gh pr checkout 7`).
Each note gives its reproduction commands. For the Lean proofs, Elan selects the
pinned toolchain and Lake reads the exact Mathlib revision from the manifest. [Install Elan][elan]

© 2026 Ali Romman · [Apache License 2.0](LICENSE) · [Cite this project](CITATION.cff)

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
[heptagon-note]: https://github.com/aliromman/math/blob/af6070cb27d25a2a18b247fdc663c5051f64aaf6/conjectures/ErdosSzekeres/README.md
[heptagon-search]: https://github.com/aliromman/math/blob/af6070cb27d25a2a18b247fdc663c5051f64aaf6/conjectures/ErdosSzekeres/replay.py
[pr9]: https://github.com/aliromman/math/pull/9
[tree-roots]: https://github.com/aliromman/math/blob/d8125823f3d4f0fee6eab50268fcfe85b946b2d6/conjectures/GeorgeTreeDegreeRoots/Solution.lean
[pr10]: https://github.com/aliromman/math/pull/10
[lucas]: https://github.com/aliromman/math/blob/4ce07db1acfbbb5bd8ddfeab3d7af2d872af13f6/conjectures/SunLucasRatios/Solution.lean
[pr11]: https://github.com/aliromman/math/pull/11
[rational-roots]: https://github.com/aliromman/math/blob/01e30f9a10ba840fd054fed0f05ac4c74058c3fd/conjectures/GeorgeRationalDegreeRoots/Solution.lean
[pr12]: https://github.com/aliromman/math/pull/12
[packing]: https://github.com/aliromman/math/blob/023ef6dd3b04f47cff626ba3f3934944d2d56073/conjectures/WordPacking121/Proof.lean
[pr13]: https://github.com/aliromman/math/pull/13
[weighted]: https://github.com/aliromman/math/blob/88f5820fb6d4b5e9eca3dcff46822153b3559080/conjectures/LiuWeightedRadicals/Solution.lean
[pr14]: https://github.com/aliromman/math/pull/14
[median]: https://github.com/aliromman/math/blob/7576bcad4a477a06d2ac3bf7dac9a47bc65d349e/conjectures/LiuMedianRatio/Solution.lean
[pr15]: https://github.com/aliromman/math/pull/15
[prime-powers]: https://github.com/aliromman/math/blob/988b03fe2a75c27a89509ca129a51edfd1ce7bac/conjectures/SunPrimePowers/Solution.lean
[pr16]: https://github.com/aliromman/math/pull/16
[layered]: https://github.com/aliromman/math/blob/d6b5369d85db40748279807719772d11f2786792/conjectures/LayeredWordPacking/Proof.lean
[pr17]: https://github.com/aliromman/math/pull/17
[group-cycles]: https://github.com/aliromman/math/blob/d06e00ea8bcc75041df81a07c50f1e8ef2547ff8/conjectures/SunCircularDifferences/Solution.lean
[pr18]: https://github.com/aliromman/math/pull/18
[real-cycles]: https://github.com/aliromman/math/blob/552d4bd30d34ea91fb052fb108e1333a9538433b/conjectures/SunRealCycles/Solution.lean
[pr19]: https://github.com/aliromman/math/pull/19
[pulls]: https://github.com/aliromman/math/pulls?q=is%3Apr+sort%3Acreated-desc
[elan]: https://github.com/leanprover/elan
