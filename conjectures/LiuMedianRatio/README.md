# Disproof of Liu’s Conjecture 1 on the median refinement of the Erdős–Mordell inequality

Take $A=(0,0)$, $B=(9,0)$, $C=(4,1/10)$, and $P=(4,1/1000)$. The sum of the distances from $P$ to the vertices, divided by the sum of its perpendicular distances to the opposite sides, is less than $45.84$. The proposed lower bound exceeds $45.89$.

For any interior point of any triangle, Liu conjectured

$$
\frac{PA+PB+PC}{r_1+r_2+r_3}
\ \ge\ \frac{4R(m_a+m_b+m_c)}{a^2+b^2+c^2}.
$$

Here $(a,b,c)=(BC,CA,AB)$ and $r_1,r_2,r_3$ are the perpendicular distances from $P$ to the lines $BC,CA,AB$, respectively. The quantity $R$ is the circumradius, and $m_a,m_b,m_c$ are the lengths of the medians from $A,B,C$ to the midpoints of the opposite sides. This would strengthen the classical Erdős–Mordell lower bound of $2$ by a quantity that depends on the shape of the triangle. [Jian Liu, *An improved result of a weighted trigonometric inequality in acute triangles with applications*, Conjecture 1, equation (68), p. 158 (2020)](https://files.ele-math.com/articles/jmi-14-11.pdf#page=12)

## Proof

The point $P$ is strictly between $C$ and its perpendicular projection on $AB$. The coordinates give

$$
a^2=25.01,\quad b^2=16.01,\quad R=5ab,\quad
(r_1,r_2,r_3)=(0.495/a,0.396/b,0.001).
$$

Each median is at least its horizontal projection in absolute value, so their sum is at least $6.5+7+0.5=14$. Since $a\ge5$ and $b\ge4$, the proposed bound is at least $5600/122.02>45.89$.

The vertex distances sum to at most $4.001+5.001+0.099=9.101$. Also $a<5.01$ and $b<4.01$. The actual ratio is therefore at most

$$
\frac{9.101}{0.495/5.01+0.396/4.01+0.001}<45.84.
$$

Every decimal in these bounds is an exact rational number. The example uses an obtuse triangle, which equation (68) explicitly permits. Searches by the formula, the source title, and related work on median refinements found no earlier disproof.

## Verification

From the repository root run

```sh
# Run at the merge commit for PR #15.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The Lean statement uses all four points in Cartesian coordinates. The proof checks strict interiority, the distance bounds, and the axiom list. OpenAI Codex found the counterexample and wrote the proof.
