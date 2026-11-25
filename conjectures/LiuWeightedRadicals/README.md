# An isosceles counterexample to Liu’s weighted Erdős–Mordell bound

The isosceles triangle with vertices $(-1,0),(1,0),(0,84/13)$ and interior point $P=(0,60/11)$ violates the proposed upper bound at $k=3999/1000$.

Let $R_i$ be the distances from $P$ to the three vertices, $r_i$ the perpendicular distances to their opposite sides, and $a_i$ the lengths of those sides. Set $w_i=\sqrt{a_i^2+kr_i^2}$. Liu conjectured that every triangle and every interior point satisfy

$$
2\sum_i r_i \ \le\ \frac{2\sum_i(R_i+r_i)w_i}{\sum_i w_i}\ \le\ \sum_i R_i
\qquad (0<k<4).
$$

The last inequality fails. The point and triangle have rational distances because the two right triangles in the construction have leg and hypotenuse ratios $13:84:85$ and $11:60:61$. [Jian Liu, *Refinements of the Erdös–Mordell inequality, Barrow’s inequality, and Oppenheim’s inequality*, Conjecture 6.4, equation (6.6) (2016)](https://doi.org/10.1186/s13660-015-0947-2)

## Proof

The side lengths are $(85/13,85/13,2)$. The vertex distances and the distances to opposite sides are

$$
(R_1,R_2,R_3)=(61/11,61/11,144/143),\qquad
(r_1,r_2,r_3)=(144/935,144/935,60/11).
$$

Write $u=w_1=w_2$ and $v=w_3$. On clearing the positive denominator, the upper bound requires $118v/143\le16992u/12155$. Both sides are positive. Substituting the values of $u^2$ and $v^2$ gives

$$
\left(\frac{118v}{143}\right)^2-\left(\frac{16992u}{12155}\right)^2
=\frac{1360460663710552}{248048828672734375}>0.
$$

This disproves the proposed two-sided refinement. The construction tests the upper bound near the endpoint $k=4$ while keeping $k$ strictly inside the stated interval. Searches by source title, conjecture number, and formula found no earlier counterexample to (6.6).

## Verification

From the repository root run

```sh
lake build
lake env leanchecker conjectures.LiuWeightedRadicals.Solution
```

The Lean statement uses Cartesian distances and strict interior tests for both triangle orientations. The proof checks the rational comparison and the theorem’s axiom list. OpenAI Codex found the witness and wrote the proof.
