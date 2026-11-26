# Partial result on Erdős Problem 107 for 33-point extensions of specified 27- and 30-point order types

In the classical 32-point example, erase any two points. Keep only the clockwise
or counterclockwise orientation of every triple of the remaining 30. A finite
SAT search excludes a heptagon-free set of 33 points with those orientations.
All 496 choices of the erased pair are covered. One particular set of just 27
points also suffices. The general 33-point question remains open.

Erdős and Szekeres asked for the least number of points in the real plane, with
no three collinear, that guarantees the vertices of a convex $k$-gon. Other
points may lie inside the polygon. They conjectured $2^{k-2}+1$ for every
$k\geq 3$. Their construction gives 32 points with no convex heptagon. Seven
is the first open polygon size. [Original conjecture, p. 464](https://www.numdam.org/item/CM_1935__2__463_0.pdf#page=3) · [Lower-bound construction](https://www.renyi.hu/~p_erdos/1960-09.pdf) · [Baek and Balko](https://doi.org/10.4230/LIPIcs.SoCG.2025.13)

## What the search excludes

Label the integer realization $p_i=(i,y_i)$ for $0\leq i<32$. The replay lists
the 32 heights in order. For the 27-point test, erase labels
$0,2,12,17,28$. All 27 retained coordinates may move as long as their triple
orientations agree. The six additional points have arbitrary positions in
general position. The corresponding Boolean formula is unsatisfiable. For
the two-deletion test, relabeling in reverse order and reflecting the plane
reduce the 496 choices to 44 orientation tables. Two encodings agreed on all
44. [Integer coordinates, §2.4](https://erdosproblemaday.com/report/107)

The extra point $(-1,-6)$ illustrates how close the classical construction
comes. There is exactly one convex heptagon. Its vertices are the seven points

$$
\left(x,\frac{11x-x^2}{2}\right),\qquad x=-1,0,1,2,3,4,5.
$$

One-point saturation of the classical construction was already known, and
33-point examples with one convex heptagon have been reported independently.
[Damásdi et al.](https://doi.org/10.4230/LIPIcs.SoCG.2024.46) · [Georgiev et al., §38](https://arxiv.org/html/2511.02864v3#S38)

## Why the computation applies to geometry

The variables give the sign $[a,b,c]$ of each oriented triangle. At a point $p$,
choose a reference ray with vector $E$. For each other ray vector $A$, the ratios
$(E\cdot A)/\det(E,A)$ have a strict order. The sign of the difference for
rays $A,B$ is the product of the signs of $\det(E,A)$, $\det(E,B)$ and
$\det(A,B)$. The replay enforces transitivity and labels the new points by this
order at one pivot.

For four points the signs of their affine dependence are
$([b,c,d],-[a,c,d],[a,b,d],-[a,b,c])$. A two-against-two split means the
four points form a convex quadrilateral. Seven points form a convex heptagon
exactly when all their four-point subsets are convex. Indeed, any interior
point lies in a triangle of three of the others. The formula requires each
seven-point subset to contain a nonconvex quadruple. It also excludes a new
point that sees exactly one edge of a convex hexagon of retained points.
Every real counterexample containing the prescribed orientations would give
a satisfying assignment.

## Reproduce

From the repository root, build the exact Lean statement. Generate the default
27-point test with Python 3 and solve it with the CaDiCaL executable included
with Lean.

```sh
lake exe cache get
python3 scripts/verify.py
mkdir -p scratch
python3 conjectures/ErdosSzekeres/replay.py 33 > scratch/heptagon.cnf
lake env cadical -q --lrat --no-binary scratch/heptagon.cnf scratch/heptagon.lrat
curl -fsSLo scratch/lrat-check.c https://raw.githubusercontent.com/marijnheule/drat-trim/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/lrat-check.c
cc -O2 scratch/lrat-check.c -o scratch/lrat-check
scratch/lrat-check scratch/heptagon.cnf scratch/heptagon.lrat
```

CaDiCaL 2.1.2 reports `UNSATISFIABLE` and exits with status 20. The independent
LRAT checker reports `VERIFIED`. Use `32` in place of `33` for the satisfiable
control. Use `pairs` to print the 44 representative deletion pairs, then
`33 --omit i j` to generate the instance for a chosen pair. [LRAT checker source](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/lrat-check.c)

Codex and collaborating AI agents designed the searches and checked the
geometric encoding. A separate search made 101 complete plane-arrangement
scans, covering 11,015,962 placement regions across the scans in about 1 minute.
Each scan reached a minimum of one heptagon. A search using small clusters
around eight centers also found no counterexample. An unrestricted search
in projective coordinates stopped after about 1 CPU minute without a decision.
Lean checks the original conjecture statement.
The finite exclusions have Boolean certificates. A Lean proof of the geometric
exclusions and a resolution of the conjecture are both open tasks.

The Erdős Problems catalogue lists the original convex-polygon conjecture as [Erdős Problem 107](https://www.erdosproblems.com/107).
