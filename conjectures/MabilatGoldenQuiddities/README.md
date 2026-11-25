# Irreducible golden-ratio quiddities have length four or five

Let $\varphi=(1+\sqrt5)/2$. The complete list of irreducible $\lambda$-quiddities with entries in $\mathbb Z\varphi$ is

$$
\pm(\varphi,\varphi,\varphi,\varphi,\varphi),\qquad
(0,k\varphi,0,-k\varphi),\qquad (k\varphi,0,-k\varphi,0)
\quad(k\in\mathbb Z).
$$

This proves Flavien Mabilat’s 2022 conjecture. These sequences give all the indivisible pieces for the matrix equation that occurs in Coxeter’s frieze patterns. [Original conjecture, p. 7, and definitions, p. 3](https://arxiv.org/pdf/2212.03142).

## Why the list ends here

Write $k$ for the entry $k\varphi$ and set

$$
A_k=\begin{pmatrix}k\varphi&-1\\1&0\end{pmatrix}.
$$

A nonempty sequence is a quiddity if $A_{k_n}\cdots A_{k_1}=\pm I$. Two sequences can be glued by adding opposite endpoints and keeping both interiors. A quiddity of length at least three is reducible if a rotation of it or its reversal is such a gluing, with each piece of length at least three and the second piece a quiddity.

**Every quiddity contains a zero or three consecutive copies of the same sign $s\in\{-1,1\}$.** To see this, start the first matrix column at $(1,0)$ and track its slope $r$. The next entry $k$ replaces $r$ with $1/(k\varphi-r)$. If no zero or forbidden triple occurs, the signed slope $sr$ stays below or equal to the following bounds.

| Number of consecutive copies of $s$ at the end | 0 | 1 | 2 |
| --- | --- | --- | --- |
| Upper bound on $sr$ | $1/\varphi$ | $1$ | $\varphi$ |

For $k=s$, the identities $\varphi-1/\varphi=1$ and $\varphi-1=1/\varphi$ give the next bound. For $sk\ge2$, the signed denominator is at least $2\varphi-\varphi=\varphi$. For $sk<0$, the new signed slope is negative. Thus the top coordinate of every prefix stays nonzero. After the last step the bottom coordinate is the preceding top coordinate. But the bottom-left entry of $\pm I$ is zero.

A consecutive pair $(0,k)$ is the interior of the quiddity $(-k,0,k,0)$. A triple $(s,s,s)$ is the interior of $(s,s,s,s,s)$. In either case, if at least three entries remain, subtract the endpoints of this shorter quiddity from the adjacent entries to undo the gluing.

It remains to check the short sequences. Length three would require an integer multiple of $\varphi$ to equal $\pm1$. At length four, three equal signs give a nonzero bottom-left entry, while $(0,x,y,z)$ forces $y=0$ and $z=-x$. At length five, a zero gives a reduction, and the product for $(s,s,s,a,b)$ forces $a=b=s$. The four-term solutions cannot split because no three-term quiddity exists. A decomposition of a constant five-term solution would require a three-term quiddity or a four-term quiddity $(c,s,s,d)$. The latter has bottom-right entry $1-\varphi^2=-\varphi$.

## Prior work and verification

Mabilat already proved irreducibility of the constant five-term examples. Holm and Jørgensen classified positive friezes by polygon dissections. Short and Walker studied geodesic continued fractions for the corresponding Hecke group. The new step here proves exhaustiveness for arbitrary signed integer multiples of $\varphi$. A search of these papers and later quiddity literature found no earlier proof of this classification. [Mabilat, Proposition 3.13](https://doi.org/10.5802/cml.98) · [Holm and Jørgensen](https://doi.org/10.1093/imrn/rny020) · [Short and Walker](https://oro.open.ac.uk/46766/1/hecke13.pdf).

Lean represents each real multiple by its unique integer coefficient. The real matrices have the same products after embedding them in $\mathbb C$. `Statement.lean` defines the source’s equation and gluing operation. `Ear.lean` proves the slope bound, and `Solution.lean` proves the classification and checks its axioms. From the repository root, run

```sh
lake build conjectures.MabilatGoldenQuiddities.Solution
lake env leanchecker conjectures.MabilatGoldenQuiddities.Solution
```

AI agents derived the proof, wrote the Lean formalization, and checked the mathematical literature.
