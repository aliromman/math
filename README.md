# Mathematical conjectures

Proofs, counterexamples, and partial results on published mathematical conjectures. Ali Romman created and maintains the collection. OpenAI Codex assisted with the research and Lean 4 formalizations.

[Research ledger and cumulative statistics](research/ledger.md)

## Verification

Install Elan, then run the following commands from a clean checkout. The first
command gets the build files for the pinned Mathlib release.

```sh
lake exe cache get
python3 scripts/verify.py
python3 scripts/test_verify.py
python3 scripts/test_selection.py
```

Lake builds the research library with warnings as errors. The verifier calls the pinned
`leanchecker` routine in a separate process for each module in the source tree. It checks
that all required object files exist, replays private proof bodies, and
traces the dependencies of every local declaration. Research proofs need
theorem names so the compiler retains them for replay. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

On pull requests, CI compares the tested merge commit with its first parent. It rebuilds changed research modules and their transitive importers, replays their proofs, and checks the full axiom contract in each affected directory. Edits to documentation alone pass after the verifier checks whether research sources use the changed files. Changes to the toolchain, dependencies, or verifier require a full check. Select **Run workflow** in the Lean workflow to audit the entire revision. To reproduce a pull request check locally, run `python3 scripts/verify.py --base BASE --fetch-cache`, where `BASE` is the tested base commit.

Each research directory with Lean sources has an `axioms` file. Each line
gives a result's qualified theorem name followed by its exact transitive
axioms, separated by spaces. A theorem with no axioms has only its name on
the line. A line that starts with `statement` can register the definition
of an open question. The research note identifies what the proof establishes
and cites the original source.

## Discoveries

Each title links to a research note. Results on this branch link to local files. Open drafts link to fixed revisions. The pull request records the review and verification history.

| Research note | Finding | Proof / PR |
| --- | --- | --- |
| [Proof of Ulas’s Conjecture 4.4 on real zeros of Stern polynomials][note-70] | Every real value in Ulas’s family is positive. Its possible prime divisors at integer arguments are exactly the primes congruent to one modulo three. | [Positivity][proof-70] · [Prime divisors][arith-70] · [#70][pr-70] |
| [Disproof of Dossou-Olory and Wagner’s conjecture on four-branch extremizers for the inducibility of the five-leaf tree A₅][note-31] | A root rotation increases the limiting density of the five-leaf tree in every proposed four-branch sequence. Its exact inducibility remains open. | [Lean][proof-31] · [#31][pr-31] |
| [Proof of Pirzada, Naikoo and Chishti’s Conjecture 2.1 on bipartite score sets][note-60] | Every nonempty finite set of positive integers is the full set of scores of an oriented bipartite graph. | [Lean][proof-60] · [#60][pr-60] |
| [Disproof of the Brosch–Puges double-caterpillar conjecture on tree profiles (Conjecture 1)][note-34] | For every $k\ge7$, joining three caterpillars beats the proposed two-caterpillar boundary. The cases $k=4,5,6$ remain open. | [Lean][proof-34] · [#34][pr-34] |
| [Solution to Haslegrave’s Question 3 on exclusive sum numbers and bounded sum index][note-56] | A finite graph with sum index $s$ has exclusive sum number at most $s3^{s-1}$. | [Lean][proof-56] · [#56][pr-56] |
| [Disproof of Hur and Kim’s fair dice conjecture (Conjecture 1)][note-32] | Three fair eight-sided dice stay fixed under both Hur–Kim moves, and their word cannot start with the proposed six-letter palindrome. | [Lean][proof-32] · [#32][pr-32] |
| [Disproof of Fang’s Conjecture 5.7 on the length of a most frequent subsequence][note-42] | A word of length ten has a unique most frequent subsequence of length six. A binary example also violates the proposed length bound. | [Lean][proof-42] · [#42][pr-42] |
| [Four-factor counterexamples to Gatzweiler and Krattenthaler’s Conjecture 4][note-36] | **Extension.** A four-factor family gives a negative coefficient. Earlier counterexamples had already disproved the conjecture. | [Lean][proof-36] · [#36][pr-36] |
| [Proof of Černý’s Conjecture 34 on counting fair words][note-35] | At each positive length $n$, the fair-word count is a monic integer polynomial of degree $\lceil n/2\rceil$ in the alphabet size. | [Lean][proof-35] · [#35][pr-35] |
| [Disproof of the Aliste-Prieto–de Mier–Zamora conjecture on the smallest trees with the same restricted U-polynomial][note-7] | Two 32-vertex trees agree through five cuts. The predicted minimum fails at every depth $m\ge5$, and the minimum is at most $3(m+1)^2$ for $m\ge1$. | [Bound][bound-7] · [Threshold][proof-7] · [#7][pr-7] |
| [Proof of Kölbl’s Conjecture 3 on canonical-line Ehrhart roots of reflexive polytopes with unimodal numerators][note-21] | Among reflexive lattice polytopes with unimodal Ehrhart numerator, the standard reflexive simplex attains the greatest root height on $\operatorname{Re}z=-1/2$ in every positive dimension. | [Lean][proof-21] · [#21][pr-21] |
| [Proof of Brown and Cameron’s Conjecture 4.2 on the maximum modulus of independence roots of graphs][note-29] | For a graph on $n\ge3$ vertices, every independence root has modulus at most $\max(p_1\cdots p_r+r)$ over all partitions $p_1+\cdots+p_r=n-1$ into positive integers. | [Lean][proof-29] · [#29][pr-29] |
| [Disproof of the pointwise bound in Sobolewski’s Conjecture 2 on monochromatic progressions in binary pattern sequences][note-27] | For every integer $j\ge5$, the binary pattern `1` followed by $j$ zeros gives a monochromatic arithmetic progression of at least $2^j$ terms where the predicted bound is below 17. | [Lean][proof-27] · [#27][pr-27] |
| [Disproof of Bajnok’s Conjecture 7 on extremizers for restricted sumsets in finite abelian groups][note-28] | Up to affine equivalence, exactly two eight-element sets modulo 17 have only 16 sums of three distinct elements. One is an interval. The other consists of the nonzero squares. | [Lean][proof-28] · [#28][pr-28] |
| [Proof of the Akbari–Oboudi conjecture on distinct edge-cover roots and minimum degree][note-20] | A finite simple graph of minimum degree $d$ has at least $d$ distinct complex roots in its edge-cover polynomial. | [Lean][proof-20] · [#20][pr-20] |
| [Proof of Brown and Cameron’s Conjecture 4.4 on the maximum modulus of independence roots of even-order trees][note-25] | For a tree on $2k$ vertices with $k\ge3$, every root of the independence polynomial has modulus at most $2^{k-2}+k+1$. | [Lean][proof-25] · [#25][pr-25] |
| [Solution to the generalized-permutohedron part of Defant’s Question 6.1 on real-rooted Narayana sums][note-22] | A translated Fano matroid base polytope has 28 lattice points and a Narayana sum with four nonreal roots. | [Lean][proof-22] · [#22][pr-22] |
| [Proof of the Burstein–Hästö–Mansour conjecture on the packing density of the vincular pattern 12-1][note-13] | Two letters attain the exact maximum of $\lfloor n(n-1)/6\rfloor$ occurrences at every word length $n$. The packing density is $1/3$. | [Lean][proof-13] · [#13][pr-13] |
| [Solution to George’s problem on the rational degree roots of graphs of a given order][note-12] | For coprime positive integers $p,q$, some simple graph on $n\ge1$ vertices has root $-p/q$ exactly when $p+q$ divides odd $n$ or $2(p+q)$ divides even $n$. | [Lean][proof-12] · [#12][pr-12] |
| [Proof of Bagchi and Zhou-Zheng’s Conjecture 12 on sporadic shifts without triangular Diophantine pairs][note-23] | For every integer $k\ge0$, adding $2\cdot7^{6k+2}$ to a product of two positive triangular numbers gives a nonsquare. | [Lean][proof-23] · [#23][pr-23] |
| [Solution to Questions 4.1 and 4.2 of Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio on Buchweitz sets][note-24] | A numerical semigroup has obstructions precisely at orders 2 and 4. Its excess counts at orders 2, 3, and 4 also disprove the proposed unimodality. | [Lean][proof-24] · [#24][pr-24] |
| [Disproof of the finite layered-maximizer assertion in Burstein, Hästö and Mansour’s Conjecture 2.8][note-17] | The word `111342222` contains 61 occurrences of `11123`, `13222`, and `11322` in total. Every layered word of the same length on the same four-letter alphabet has at most 60. | [Lean][proof-17] · [#17][pr-17] |
| [Proof of George’s Conjecture 1 on nonreal degree roots of trees in the unit disk][note-10] | Every nonreal root of a finite tree’s degree polynomial has modulus greater than one. | [Lean][proof-10] · [#10][pr-10] |
| [Disproof of Sun’s Conjecture 3.3(ii) on distinct cyclic differences in finite abelian groups of odd order][note-18] | Remove any two elements from an abelian group of odd order $N\ge5$. Every circular ordering of the rest repeats a directed difference between neighbors. | [Lean][proof-18] · [#18][pr-18] |
| [Disproof of Sun’s Conjecture 3.10(ii) on simultaneous distinct differences and products in a circular order][note-19] | Every circular order of four distinct positive numbers repeats a directed difference or adjacent product exactly when the middle two are the harmonic and arithmetic means of the extremes. | [Lean][proof-19] · [#19][pr-19] |
| [Disproof of the Engbers–Erey conjecture on maximum average maximal-matching size in trees of fixed order and diameter][note-1] | Moving one leaf in a 15-vertex tree preserves diameter 11 and raises the mean size of a maximal matching from $6$ to $259/43$, disproving the proposed maximum. | [Lean][proof-1] · [#1][pr-1] |
| [Proof of Liu’s Conjecture 1 on Walker’s inequality with side-power weights][note-2] | The cyclic inequality with side weight $a^k$ holds on every nonobtuse triangle for all real $k\le4$. | [Lean][proof-2] · [#2][pr-2] |
| [Proof of Liu’s Conjecture 2 on Walker’s inequality with side-sum weights][note-3] | The cyclic inequality with side-sum weight $(b+c)^k$ holds on every nonobtuse triangle for all real $k\ge-10$. | [Lean][proof-3] · [#3][pr-3] |
| [Proof of Liu’s Conjecture 3 on Walker’s inequality with triangle-excess weights][note-4] | The cyclic inequality with weight $(b+c-a)^k$ holds on every nonobtuse triangle for all real $k\ge-3$. | [Lean][proof-4] · [#4][pr-4] |
| [Disproof of Sun’s Conjecture 2.1 on a real-power extension of Mandl’s inequality using Panaitopol’s nine-prime example][note-16] | The first nine primes at exponent $1/2000$ violate the proposed real-power extension of Mandl’s inequality. | [Lean][proof-16] · [#16][pr-16] |
| [Disproof of the Lucas-sequence assertion in Sun’s Conjecture 3.1 on successive root ratios][note-11] | For the Lucas sequence with parameters $(A,B)=(3,-26)$, the ratio $u_{n+1}^{1/(n+1)}/u_n^{1/n}$ increases from $n=5$ to $n=6$. | [Lean][proof-11] · [#11][pr-11] |
| [Disproof of Liu’s Conjecture 6.4 on weighted Erdős–Mordell bounds for an interior point][note-14] | An isosceles triangle and an interior point violate the proposed upper bound at $k=3999/1000$. | [Lean][proof-14] · [#14][pr-14] |
| [Disproof of Liu’s Conjecture 1 on the median refinement of the Erdős–Mordell inequality][note-15] | At an interior point of a thin obtuse triangle, the sum of vertex distances divided by the sum of side distances is below $45.84$. The proposed lower bound exceeds $45.89$. | [Lean][proof-15] · [#15][pr-15] |
| [Partial result on Erdős Problem 107 for 33-point extensions of specified 27- and 30-point order types][note-9] | **Partial.** A finite SAT search rules out a heptagon-free 33-point extension of one specific 27-point pattern of triple orientations. The general question remains open. | [Search][proof-9] · [#9][pr-9] |
| [Two-site branch exchanges and a finite three-site search in Stanley’s tree isomorphism question][note-6] | **Partial.** A two-site branch exchange cannot produce nonisomorphic trees with the same chromatic symmetric function. A separate search distinguished 111,144 trees in a three-site family. | [Search][proof-6] · [#6][pr-6] |

Follow the reproduction commands in the research note. For an open draft, check out the linked pull request first. [Install Elan][elan]

© 2026 Ali Romman · [Apache License 2.0](LICENSE) · [Cite this project](CITATION.cff) · [All pull requests][pulls]

[note-29]: https://github.com/aliromman/math/blob/f4bee61ac4d3435fcb9739ef5fac753b5a99e521/conjectures/BrownCameronGraphModulus/README.md
[proof-29]: https://github.com/aliromman/math/blob/f4bee61ac4d3435fcb9739ef5fac753b5a99e521/conjectures/BrownCameronGraphModulus/Solution.lean
[pr-29]: https://github.com/aliromman/math/pull/29
[note-28]: https://github.com/aliromman/math/blob/1978df3cbab28d706239fd31351e15c0d03657c3/conjectures/BajnokRestrictedInverse/README.md
[proof-28]: https://github.com/aliromman/math/blob/1978df3cbab28d706239fd31351e15c0d03657c3/conjectures/BajnokRestrictedInverse/Solution.lean
[pr-28]: https://github.com/aliromman/math/pull/28
[note-25]: https://github.com/aliromman/math/blob/62a8ea73c9cbff20832ea52cfa1556c63a2ad028/conjectures/BrownCameronEvenTrees/README.md
[proof-25]: https://github.com/aliromman/math/blob/62a8ea73c9cbff20832ea52cfa1556c63a2ad028/conjectures/BrownCameronEvenTrees/Solution.lean
[pr-25]: https://github.com/aliromman/math/pull/25
[note-22]: https://github.com/aliromman/math/blob/a5cb492a3b08718764bed02a2831dba979c9402f/conjectures/DefantNarayana/README.md
[proof-22]: https://github.com/aliromman/math/blob/a5cb492a3b08718764bed02a2831dba979c9402f/conjectures/DefantNarayana/Solution.lean
[pr-22]: https://github.com/aliromman/math/pull/22
[note-24]: https://github.com/aliromman/math/blob/212750d415b40370dad8f0e2aa482fd071cf1bf6/conjectures/BuchweitzGapset/README.md
[proof-24]: https://github.com/aliromman/math/blob/212750d415b40370dad8f0e2aa482fd071cf1bf6/conjectures/BuchweitzGapset/Solution.lean
[pr-24]: https://github.com/aliromman/math/pull/24
[note-17]: https://github.com/aliromman/math/blob/d6b5369d85db40748279807719772d11f2786792/conjectures/LayeredWordPacking/README.md
[proof-17]: https://github.com/aliromman/math/blob/d6b5369d85db40748279807719772d11f2786792/conjectures/LayeredWordPacking/Proof.lean
[pr-17]: https://github.com/aliromman/math/pull/17
[note-15]: https://github.com/aliromman/math/blob/7576bcad4a477a06d2ac3bf7dac9a47bc65d349e/conjectures/LiuMedianRatio/README.md
[proof-15]: https://github.com/aliromman/math/blob/7576bcad4a477a06d2ac3bf7dac9a47bc65d349e/conjectures/LiuMedianRatio/Solution.lean
[pr-15]: https://github.com/aliromman/math/pull/15
[pulls]: https://github.com/aliromman/math/pulls?q=is%3Apr+sort%3Acreated-desc
[elan]: https://github.com/leanprover/elan
[note-1]: conjectures/EngbersErey/README.md
[proof-1]: conjectures/EngbersErey/Solution.lean
[pr-1]: https://github.com/aliromman/math/pull/1
[note-2]: conjectures/LiuWalkerOne/README.md
[proof-2]: conjectures/LiuWalkerOne/Solution.lean
[pr-2]: https://github.com/aliromman/math/pull/2
[note-3]: conjectures/LiuWalkerTwo/README.md
[proof-3]: conjectures/LiuWalkerTwo/Solution.lean
[pr-3]: https://github.com/aliromman/math/pull/3
[note-4]: conjectures/LiuWalkerThree/README.md
[proof-4]: conjectures/LiuWalkerThree/Solution.lean
[pr-4]: https://github.com/aliromman/math/pull/4
[note-6]: conjectures/StanleyTreeCSF/README.md
[proof-6]: conjectures/StanleyTreeCSF/replay.py
[pr-6]: https://github.com/aliromman/math/pull/6
[note-7]: conjectures/RestrictedUMinimum/README.md
[bound-7]: conjectures/RestrictedUMinimum/Growth.lean
[proof-7]: conjectures/RestrictedUMinimum/Threshold.lean
[pr-7]: https://github.com/aliromman/math/pull/7
[note-9]: conjectures/ErdosSzekeres/README.md
[proof-9]: conjectures/ErdosSzekeres/replay.py
[pr-9]: https://github.com/aliromman/math/pull/9
[note-18]: conjectures/SunCircularDifferences/README.md
[proof-18]: conjectures/SunCircularDifferences/Solution.lean
[pr-18]: https://github.com/aliromman/math/pull/18
[proof-35]: conjectures/CernyFairWords/Solution.lean
[note-35]: conjectures/CernyFairWords/README.md
[pr-35]: https://github.com/aliromman/math/pull/35
[note-27]: conjectures/SobolewskiPatternBound/README.md
[proof-27]: conjectures/SobolewskiPatternBound/Solution.lean
[pr-27]: https://github.com/aliromman/math/pull/27
[proof-36]: conjectures/GatzweilerKrattenthalerShift/Solution.lean
[note-36]: conjectures/GatzweilerKrattenthalerShift/README.md
[pr-36]: https://github.com/aliromman/math/pull/36
[note-10]: conjectures/GeorgeTreeDegreeRoots/README.md
[proof-10]: conjectures/GeorgeTreeDegreeRoots/Solution.lean
[pr-10]: https://github.com/aliromman/math/pull/10
[note-11]: conjectures/SunLucasRatios/README.md
[proof-11]: conjectures/SunLucasRatios/Solution.lean
[pr-11]: https://github.com/aliromman/math/pull/11
[proof-42]: conjectures/FangSubwordLength/Solution.lean
[note-42]: conjectures/FangSubwordLength/README.md
[pr-42]: https://github.com/aliromman/math/pull/42
[note-20]: conjectures/EdgeCoverRootCount/README.md
[proof-20]: conjectures/EdgeCoverRootCount/Solution.lean
[pr-20]: https://github.com/aliromman/math/pull/20
[proof-32]: conjectures/HurKimFairDice/Solution.lean
[note-32]: conjectures/HurKimFairDice/README.md
[pr-32]: https://github.com/aliromman/math/pull/32
[note-19]: conjectures/SunRealCycles/README.md
[proof-19]: conjectures/SunRealCycles/Solution.lean
[pr-19]: https://github.com/aliromman/math/pull/19
[note-23]: conjectures/TriangularSporadic/README.md
[proof-23]: conjectures/TriangularSporadic/Solution.lean
[pr-23]: https://github.com/aliromman/math/pull/23
[note-12]: conjectures/GeorgeRationalDegreeRoots/README.md
[proof-12]: conjectures/GeorgeRationalDegreeRoots/Solution.lean
[pr-12]: https://github.com/aliromman/math/pull/12
[proof-56]: conjectures/ExclusiveSumBound/Solution.lean
[note-56]: conjectures/ExclusiveSumBound/README.md
[pr-56]: https://github.com/aliromman/math/pull/56
[note-14]: conjectures/LiuWeightedRadicals/README.md
[proof-14]: conjectures/LiuWeightedRadicals/Solution.lean
[pr-14]: https://github.com/aliromman/math/pull/14
[proof-34]: conjectures/BroschPugesTreeProfile/Solution.lean
[note-34]: conjectures/BroschPugesTreeProfile/README.md
[pr-34]: https://github.com/aliromman/math/pull/34
[note-16]: conjectures/SunPrimePowers/README.md
[proof-16]: conjectures/SunPrimePowers/Solution.lean
[pr-16]: https://github.com/aliromman/math/pull/16
[note-21]: conjectures/KolblSimplexRoots/README.md
[proof-21]: conjectures/KolblSimplexRoots/Solution.lean
[pr-21]: https://github.com/aliromman/math/pull/21
[proof-60]: conjectures/BipartiteScoreSets/Solution.lean
[note-60]: conjectures/BipartiteScoreSets/README.md
[pr-60]: https://github.com/aliromman/math/pull/60
[proof-31]: conjectures/WagnerTreeInducibility/Solution.lean
[note-31]: conjectures/WagnerTreeInducibility/README.md
[pr-31]: https://github.com/aliromman/math/pull/31
[note-70]: conjectures/UlasStern/README.md
[proof-70]: conjectures/UlasStern/Solution.lean
[arith-70]: conjectures/UlasStern/Arithmetic.lean
[pr-70]: https://github.com/aliromman/math/pull/70
[note-13]: conjectures/WordPacking121/README.md
[proof-13]: conjectures/WordPacking121/Proof.lean
[pr-13]: https://github.com/aliromman/math/pull/13
