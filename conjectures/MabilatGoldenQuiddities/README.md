# Proof of Mabilat’s conjecture on irreducible golden-ratio quiddities

Let $\varphi=(1+\sqrt5)/2$. The complete list of irreducible $\lambda$-quiddities with entries in $\mathbb Z\varphi$ is

$$
\pm(\varphi,\varphi,\varphi,\varphi,\varphi),\qquad
(0,k\varphi,0,-k\varphi),\qquad (k\varphi,0,-k\varphi,0)
\quad(k\in\mathbb Z).
$$

This proves Flavien Mabilat’s unnumbered conjecture after Proposition 3.9 on irreducible golden-ratio quiddities. The proof gives a uniform classification. For every integer $q\ge4$, replace $\varphi$ by $\lambda=2\cos(\pi/q)$ and the two constant five-term sequences by constant $q$-term sequences. These are all the indivisible pieces for the corresponding matrix equation from Coxeter’s frieze patterns. Mabilat’s conjecture is the case $q=5$. [Original conjecture, p. 7, and definitions, p. 3](https://arxiv.org/pdf/2212.03142#page=7).

## Why the list ends here

Write $k$ for the entry $k\lambda$ and set $`A_k=\left(\begin{smallmatrix}k\lambda&-1\\1&0\end{smallmatrix}\right)`$. A nonempty sequence is a quiddity if $A_{k_n}\cdots A_{k_1}=\pm I$. Gluing adds the first endpoint of each piece to the last endpoint of the other and keeps both interiors. A quiddity of length at least three is reducible if a rotation of it or its reversal is such a gluing, with both pieces of length at least three and the second piece a quiddity.

**Every quiddity contains a zero or $q-2$ consecutive copies of the same sign $`s\in\{-1,1\}`$.** Start the first matrix column at $(1,0)$ and track its slope $r$. The next entry $k$ changes the slope to $1/(k\lambda-r)$. Put $\theta=\pi/q$ and $S_j=\sin(j\theta)/\sin\theta$. If the sequence avoids both patterns, then after a run of $j$ copies of $s$ the signed slope satisfies

$$
sr\le B_j=\frac{S_{j+1}}{S_{j+2}},\qquad 0\le j\le q-3.
$$

The recurrence $S_{j+2}=\lambda S_{j+1}-S_j$ gives $B_0=1/\lambda$, $B_j\le\lambda$, and $B_{j+1}=1/(\lambda-B_j)$ for $j<q-3$. These bounds propagate when the next entry is $s$. If $sk\ge2$, the signed denominator is at least $2\lambda-B_j\ge\lambda$. The sign opposite to $k$ has negative signed slope. Thus every prefix has a nonzero top coordinate. After the last step the bottom coordinate equals the preceding top coordinate, whereas the bottom-left entry of $\pm I$ is zero. For the golden ratio the three successive bounds are $1/\varphi,1,\varphi$.

A pair $(0,k)$ is the interior of the quiddity $(-k,0,k,0)$. A run of $q-2$ signs $s$ is the interior of the constant $q$-term quiddity. If at least three entries remain, subtract the two endpoints of the shorter quiddity from its neighbors to undo the gluing.

The remaining cases follow from the same sine recurrence. For a zero, a three-term solution would require $k\lambda=\pm1$, and a four-term solution $(0,x,y,z)$ forces $y=0$ and $z=-x$. For a run of $q-2$ signs, appending zero or one further entries leaves the bottom-left matrix entry nonzero, while appending two gives $\pm I$ only when both equal $s$. Conversely, no four-term solution splits, since there are no three-term quiddities. Splitting a constant $q$-term solution would require a quiddity $(c,s,\ldots,s,d)$ with $1\le j\le q-3$ interior signs. Its bottom-right entry has absolute value $S_{j+1}>1$.

## Prior work and verification

Mabilat proved that the constant $q$-term examples are irreducible and classified the full lists for $q=4,6$. Holm and Jørgensen classified positive frieze patterns by polygon dissections. Short and Walker characterized geodesic Rosen continued fractions in the Hecke groups. The contribution here is exhaustiveness for arbitrary signs at $q=5$ and uniformly at every $q\ge7$. A search of these papers and subsequent quiddity literature found no previous proof of these classifications. [Mabilat, Theorem 2.5 and Proposition 3.13](https://doi.org/10.5802/cml.98) · [Holm and Jørgensen](https://doi.org/10.1093/imrn/rny020) · [Short and Walker](https://oro.open.ac.uk/46766/1/hecke13.pdf).

Lean encodes each multiple of $\lambda$ by its unique integer coefficient. The real matrix product agrees with its image in $\mathbb C$. `Statement.lean` gives the source conjecture and the general theorem. `Ear.lean` proves the run bound. `Solution.lean` proves the classification, specializes it at $q=5$, and checks both theorems’ axioms. From the repository root, run

```sh
# Run at the merge commit for PR #38.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

AI agents derived the proof and wrote the Lean formalization. An independent agent checked the source definitions and the uniform proof. As a separate test, exact polynomial arithmetic verified the nonzero continuant for all 548,870 words of lengths 1 through 8 over $`\{-2,-1,1,2\}`$ that avoid the forbidden run, summed over $q=4,\ldots,10$.
