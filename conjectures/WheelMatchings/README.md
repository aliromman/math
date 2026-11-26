# Twelve points disprove the wheel maximum for perfect matchings

Twelve points on a parabola have **252** perfect matchings with exactly ten crossings. A regular 11-gon and its center have **176**. Moving a single parabola point into the convex hull gives **248**, still above the proposed maximum.

| Configuration of twelve points | Perfect matchings with ten crossings |
| --- | ---: |
| $(i,i^2)$ for $0\le i\le 11$ | 252 |
| $(i,2i^2)$ for $0\le i\le 11$, with $(1,2)$ moved to $(1,5)$ | 248 |
| Regular 11-gon and its center | 176 |

## Conjecture and consequence

Aichholzer, Fabila-Monroy, Kindermann, Parada, Paul, Perz, Schnider, and Vogtenhuber ask which sets of $n$ points in general position maximize the number of straight-line perfect matchings with exactly $k$ crossing pairs of edges. For ten points with six crossings, their computations give 72 matchings for the regular wheel and 70 in convex position. After Theorem 7 they conjecture that wheels maximize this count for $k=(n-2)(n-4)/8$, with maximum $(n-1)2^{n/2-2}$. At twelve points the proposed maximum equals 176. The two explicit point sets above exceed it. The true maximum at twelve points remains undetermined here. [Original paper, Algorithmica 86 (2024), 697–716](https://doi.org/10.1007/s00453-023-01147-7)

## Proof

Pair the lowest remaining label with each possible partner, remove these two points, and repeat. Every perfect matching has exactly one such description. For twelve points this gives $11\cdot9\cdot7\cdot5\cdot3=10{,}395$ matchings. Count an unordered pair of edges precisely when each straight line strictly separates the endpoints of the other edge.

For the parabola the signed area determinant at labels $a<b<c$ is $(b-a)(c-a)(c-b)>0$. Raising point 1 in the second set changes just the sign of the triple $(0,1,2)$. Point 1 lies inside the triangle with labels $0,2,11$, with respective barycentric weights $23/44$, $17/36$, and $1/198$. At every other label $i$, the line of slope $4i$ through that point lies strictly below all remaining points. Thus this example also has exactly one interior point.

In the regular wheel let label 0 be the center. Label the hull vertices 1 through 11 counterclockwise. Every increasing hull triple has positive determinant. For the center and hull labels $b<c$, the determinant is $\sin(2\pi(c-b)/11)$, positive exactly when $c-b\le5$. These rules determine every crossing without trigonometric approximations. Applying the pairing recursion to the three sign rules gives the counts in the table.

The convex matching counts follow from the classical Touchard–Riordan formula. The comparison with the geometric conjecture, the explicit counts for the two one-interior-point configurations, and the formal proofs were produced with OpenAI Codex. Pilz, Welzl and Wettstein describe the second order type as a barely-in wheel. Related work on wheels counts crossing-free matchings. A search of the conjecture, citations, and wheel-matching literature found no earlier disproof. [Riordan (1975)](https://doi.org/10.1090/S0025-5718-1975-0366686-9), [Ruiz-Vargas and Welzl](https://doi.org/10.1007/978-3-319-44479-6_30), [Pilz, Welzl and Wettstein](https://doi.org/10.4230/LIPIcs.SoCG.2017.54)

## Verification

From the repository root, run the following commands.

```sh
lake exe cache get
lake build conjectures.WheelMatchings.Solution
lake env leanexport conjectures.WheelMatchings.Solution -- WheelMatchings.resolution WheelMatchings.no_proposed_bound WheelMatchings.counterexample WheelMatchings.oneInterior_count WheelMatchings.exposed WheelMatchings.interior_coordinates WheelMatchings.mem_matchings WheelMatchings.matchings_nodup > wheel-proof.ndjson
lake env leanchecker --from-export wheel-proof.ndjson
```

The statement uses real planar coordinates and the determinant test for a proper intersection. The proof establishes the sign rules from those coordinates, then checks all counts in the kernel. The final theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

An independent AI reviewer checked the geometry against the paper and reproduced the three counts by a chord-opening recurrence, fixed-spoke enumeration, and direct integer determinants.
