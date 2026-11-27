# Proof of Kölbl’s Conjecture 3 on canonical-line Ehrhart roots of reflexive polytopes with unimodal numerators

Among reflexive lattice polytopes with unimodal Ehrhart numerator, the standard reflexive simplex attains the greatest height of a root on the line $\operatorname{Re}z=-1/2$, in every positive dimension. Max Kölbl proved the bound through dimension nine and asked whether unimodality suffices in higher dimensions. [Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*, Proposition 4 and Conjecture 3 (2025)](https://math.colgate.edu/~integers/z68/z68.pdf#page=12)

A lattice polytope $P$ has vertices with integer coordinates. Its Ehrhart polynomial $E_P(n)$ counts the lattice points in the dilation $nP$. In dimension $d$, write its polynomial in the binomial basis as

$$E_P(z)=\sum_{j=0}^d h_j\binom{z+d-j}{d}.$$

The coefficients $h_j$ are nonnegative integers and $h_0=1$. Reflexivity makes them symmetric. The conjecture assumes that they increase weakly to the middle and then decrease weakly. For the standard simplex with vertices $e_1,\ldots,e_d,-\sum e_i$, every $h_j=1$. The formal result also covers asymmetric coefficient sequences with a middle peak.

## Proof

Write $z=-1/2+iy$ with $y>0$ and put $D=d+1$. For $d\ge2$, let $T$ be the unique positive solution of

$$\sum_{r=0}^{d}\arctan\frac{r+1/2}{T}=\pi.$$

To see why this height controls the roots, set $C_j=\prod_{r=0}^{D-1}(z+r+1-j)$. Taking a difference of consecutive products gives $D!\binom{z+d-j}{d}=C_j-C_{j+1}$. After division by $i^d$, the real part of $C_j$ has the sign of $\sin\phi_j$, where

$$\phi_j=\sum_{r=0}^{D-1}\arctan\frac{r+1/2-j}{y}.$$

The angles decrease with $j$, and reversing the factors gives $\phi_{D-j}=-\phi_j$. At $y>T$ they all lie between $-\pi$ and $\pi$. Thus $\operatorname{Re}(C_j/i^d)$ is nonnegative in the first half and nonpositive in the second. Its first value is strictly positive.

Summation by parts gives

$$D! E_P(z)= h_0C_0+\sum_{j=1}^d(h_j-h_{j-1})C_j-h_d C_D.$$

After division by $i^d$, every term has nonnegative real part. The first term has positive real part. Hence $E_P(z)\ne0$. At $y=T$, the endpoint products have equal modulus and their arguments differ by $2\pi$, so $C_0=C_D$. For the standard simplex the sum telescopes to $C_0-C_D$, proving equality. Complex conjugation gives the lower endpoint. Dimension one follows from a linear polynomial, and dimension zero has no roots.

## Sources and verification

Kölbl gives the canonical-line formulation, the binomial expansion for the standard simplex, and computations in low dimension. Earlier work identified the extreme root of this simplex and its asymptotic growth. Searches by conjecture, simplex, and extremal root found no earlier proof of Kölbl's comparison for unimodal numerators in every dimension. [Bey, Henk and Wills, *Notes on the Roots of Ehrhart Polynomials*](https://doi.org/10.1007/s00454-007-1330-y) · [Braun and Develin, Theorem 2.2](https://arxiv.org/pdf/math/0610399#page=2)

From the repository root, run

```sh
# Run at the merge commit for PR #21.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The statement defines reflexivity by the polar lattice polytope, the Ehrhart numerator by the lattice counts of all dilations, and the canonical span by the real convex hull of the roots on the indicated line. The comparison simplex uses its explicit polynomial from the source. OpenAI Codex derived the summation-by-parts proof and wrote the Lean formalization.
