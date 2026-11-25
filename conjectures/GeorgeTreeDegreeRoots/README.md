# A tree’s degree polynomial has only real roots in the unit disk

For a finite tree $T$, form the polynomial $D_T(z)=\sum_{v\in V(T)}z^{\deg(v)}$.
Every nonreal root satisfies $|z|>1$. In particular, the degree roots of all
finite trees together miss the open upper half of the unit disk.

Ian C. George conjectured the open-disk result and its nondensity consequence.
His Proposition 3.22 proved it when the tree has sufficiently few or sufficiently
many vertices of degree two. The proof below covers every number of such vertices
and includes the boundary of the disk. [George, *On the Degree Polynomial of
Graphs* (2023), §3.4.1, Conjecture 1 and Proposition 3.22](https://dalspaceb.library.dal.ca/server/api/core/bitstreams/b38bd694-b1b7-4993-a49f-b0d2dc04cc0b/content)

## Proof

The one-vertex tree has degree polynomial $1$. In every other tree, let $a_k$
count the vertices of degree $k$. Counting the two ends of each edge gives

$$a_1=2+\sum_{k\ge3}(k-2)a_k.$$

Suppose $0<|z|\le1$ and $D_T(z)=0$. Divide by $z^2$ and take imaginary parts.
The degree-two term becomes real. For $m\ge0$, the bound
$|\operatorname{Im}(z^m)|\le m|\operatorname{Im}z|$ follows by induction from
the product formula for the imaginary part and $|z|\le1$. Thus

$$\frac{a_1}{|z|^2}|\operatorname{Im}z|
\le\sum_{k\ge3}(k-2)a_k|\operatorname{Im}z|
=(a_1-2)|\operatorname{Im}z|.$$

This forces $\operatorname{Im}z=0$.

## Prior work

Degree roots of unrestricted finite simple graphs are dense in the complex plane.
Brown and George state this in §1 and refer to George’s thesis for the study of
trees at the end of §4. Their Conjecture 4.1 bounds the modulus of a graph root in
terms of its argument and graph order. It gives no exclusion inside the unit disk.
A search by author, conjecture text, and subject found no earlier proof of the
tree conjecture. [Brown and George, *On the Roots of Degree Polynomials*
(2025)](https://ajc.maths.uq.edu.au/pdf/92/ajc_v92_p164.pdf)

## Verification

Run from the repository root.

```sh
lake build
lake env leanchecker conjectures.GeorgeTreeDegreeRoots.Solution
```

The statement defines the degree polynomial for a finite graph. The proof uses
Mathlib’s tree edge count and degree-sum formula. Its final declaration checks
the axiom list. Codex found the argument and wrote the formal proof.
