# Manuscripts and publication candidates

## Manuscripts

| Result | Contribution and prior work | Manuscript |
| --- | --- | --- |
| Erdős–Purdy–Straus, Problem 3.4 (#81) | Determines and attains the greatest ratio of the area of a convex body to the area of a largest inscribed triangle with a boundary side. The sharp value is about 2.3075689464. Fleischer, Mehlhorn, Rote, Welzl and Yap established the pentagon bound and gave a hexagon with ratio 9/4 in 1992. The paper explains why the pentagon bound suffices for the later line-transversal theorem. | [PDF](../conjectures/ErdosPurdyStraus/manuscript.pdf) · [LaTeX](../conjectures/ErdosPurdyStraus/manuscript.tex) · [Proof and sources](../conjectures/ErdosPurdyStraus/README.md) |
| Conlon–Fox–Pham, Conjecture 10 (#59) | Gives the matching lower bound for every number of colours at least three. Conlon, Fox and Pham proved the two-colour case, supplied the interval lemma used here and constructed the colouring attaining the upper bound. | [PDF](../conjectures/CFPLogDensity/manuscript.pdf) · [LaTeX](../conjectures/CFPLogDensity/manuscript.tex) · [Proof and sources](../conjectures/CFPLogDensity/README.md) |

Each manuscript gives a mathematical proof, cites its sources and describes the role of AI. Run `tectonic manuscript.tex` in either result directory to typeset it. Both drafts leave the human byline open for the authors to settle before submission.

## Other standalone candidates

| Result | Proposed scope |
| --- | --- |
| [Connected split matroids (#40)](../conjectures/SplitMatroidFlags/README.md) | A short note can give the two 11-element matroids and the single incidence that distinguishes their flag vectors. Alejandro Vargas reproduced the counts with the authors’ code. The source is a preprint and its authors intend to correct the reported search. Coordinate publication with them. |
| [Signed sets (#116)](../conjectures/BorgSignedSets/README.md) | Lead with the classification of maximum nonstars. Borg’s reduction and the weighted theorem of Chang, Liu and Liu already give the maximum size. |
| [Hypertriangulations (#87)](../conjectures/Hypertriangulations/README.md) | The local refinement and conserved quantity prove maximality at every level. The local criterion also explains how to enlarge a nonmaximal example. |
| [Directed six-cycles (#95)](../conjectures/SavchenkoSix/README.md) | The finite minimum over regular tournaments follows from a local inequality. Present the proof with its exact cycle-count conventions. |
| [Packing 2413 (#84)](../conjectures/PresuttiStromquist/README.md) | The construction beats the proposed density and rules out the proposed optimizer for all its parameter values. The exact packing density remains open. |
| [Dual pairs in flag complexes (#114)](../conjectures/OlarteSantosSpreerStump/README.md) | A short counterexample addresses the proposed dual-pair classification. The separate EKR conjecture on maximum intersecting facet families remains open. |
| [Polyomino ideals (#64)](../conjectures/PolyominoPrimality/README.md) | Give the printed common-rectangle condition, the alternative opposite-corner test and the 13-cell example over every field. The authors are investigating the example and their implementation. Independent confirmation by them is pending. |
| [Optimal Bernoulli laws (#96)](../conjectures/BekkOrder/README.md) | Lead with the corrected interval-tiling theorem for interior biases. A degenerate endpoint accounts for the failure of the printed statement. |

## Contributions to combine

| Proposed paper | Reason to combine |
| --- | --- |
| Peak-polynomial zeros, [#117](../conjectures/PeakRootBounds/README.md) and [#118](../conjectures/BilleyFahrbachTalmageClassification/README.md) | The two conjectures share the permutation counts, normalization and growth estimates. Present Li’s contribution to the disk bound and the original authors’ six real-rooted families before the real-part estimate and converse classification. |
| Markov polynomial coefficients, [#85](../conjectures/MarkovFactorFour/README.md) and [#86](../conjectures/MarkovNearestFour/README.md) | The Farey recurrence explains both divisibility by four in the critical triangle and the position of a coefficient equal to four. |
| Missing sums, [#66](../conjectures/MissingSumFringes/First/README.md) and [#67](../conjectures/MissingSumFringes/Longest/README.md) | The first sum and the longest interval depend on the same random fringes. Keep the authors’ differing versions of the second question explicit. |
| Gallian–Rusin dice, [#62](../conjectures/GallianRusinDice/README.md), [#63](../conjectures/GallianRusinGame/README.md) and [#65](../conjectures/GallianRusinPrimeSquare/README.md) | A common cyclotomic method gives three classifications. The 30-sided exceptional die, the 105-sided list and the uniform prime-square theorem remain separate statements. The two finite classifications share their coefficient tables and unit-circle estimates in Lean. |
| Bajnok’s restricted sums, [#28](../conjectures/BajnokRestrictedInverse/README.md) and [#115](../conjectures/BajnokRestrictedMinimum/README.md) | Present the inverse classification modulo 17 and the failure of the proposed minimum modulo 444 as two distinct results. The latter uses Bajnok’s seven-element example as a building block. |
| Karlovsky’s distinct factors, [#77](../conjectures/KarlovskySumBound/README.md) and [#78](../conjectures/KarlovskySumAttainment/README.md) | The second theorem determines precisely when the bound in the first is attained and identifies the maximizing tuple. |
| Independence roots, [#25](../conjectures/BrownCameronEvenTrees/README.md) and [#29](../conjectures/BrownCameronGraphModulus/README.md) | Brown and Cameron ask for the maximum root modulus for graphs and a sharper bound for even-order trees. The proofs share coefficient estimates. |
| Walker inequalities, [#2](../conjectures/LiuWalkerOne/README.md), [#3](../conjectures/LiuWalkerTwo/README.md) and [#4](../conjectures/LiuWalkerThree/README.md) | Liu’s three inequalities use distinct weights. One account can compare the admissible exponents and the common triangle argument while retaining the three source statements. |

The 13-gon result in [#93](../conjectures/PolygonEhrhart/README.md) belongs as a formalization of the October solutions. The quadrilateral example in [#75](../conjectures/StrausBoundaryPolygon/README.md) extends an earlier triangular counterexample. It can accompany a study of polygon variants if its specific contribution is clear. The remaining notes have source and priority records in the [result-by-result audit](audit.md).

## Separate asymptotic result

The review of Erdős Problem 708 gives the sharp limit for the worst-case selection budget. It combines the upper bound proposed in PR 120 with a formalization of the 1959 Erdős–Surányi lower bound. Their paper credits Tibor Gallai with the selection problem in 1948. The stronger pointwise bound remains open. The notes and eight theorem contracts are on a separate review branch. [Argument and attribution](https://github.com/aliromman/math/blob/24ab10088d0166c28e6729969e383c4e52dd61fb/conjectures/ErdosSuranyi708/README.md) · [PR 120, open draft](https://github.com/aliromman/math/pull/120) · [1959 paper](https://users.renyi.hu/~p_erdos/1959-07.pdf)
