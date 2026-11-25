# A Fano-plane counterexample to real-rooted Narayana sums

An integral generalized permutohedron can have a Narayana sum with four nonreal roots. Our example has 28 lattice points. Its polynomial is

$$
4x^7(1+x)^2(7x^4+37x^3+63x^2+37x+7).
$$

For $x\ne0$, divide the quartic by $x^2$ and set $y=x+1/x$. The result is $7y^2+37y+49$, whose discriminant is $-3$.

Colin Defant asked whether every integral generalized permutohedron in the positive orthant has a real-rooted Narayana sum. This is the second question in *Fertilitopes*, Question 6.1. The first question concerns nestohedra and remains separate. Defant returns to both questions in Section 9.2 of his subsequent paper and proves log-concavity for Narayana sums of translated matroid base polytopes. [Original paper](https://doi.org/10.1007/s00454-023-00488-y) · [Subsequent paper](https://arxiv.org/html/2611.13479#S9.SS2)

## The 28 points

Take the seven nonzero vectors in $\mathbb F_2^3$. Fix a line $A$ of the Fano plane, which consists of the three nonzero vectors of a two-dimensional subspace. Write $\mathbf 1_S$ for the indicator vector of a set $S$. For each linearly independent triple $B$, take the point

$$
q_B=\mathbf 1+\mathbf 1_A+\mathbf 1_B.
$$

Their convex hull is a translate of the Fano matroid base polytope, hence an integral generalized permutohedron. Each coordinate ranges over two consecutive integers. At an integer point of this hull, a convex combination must use points that agree in every coordinate, so the displayed points are all its lattice points.

The values $k=|A\cap B|$ occur with frequencies $4,12,12$ for $k=0,1,2$. Each triple outside $A$ is independent. For $k=1$, among the three choices of a point on $A$ for each outside pair, precisely one completes its line. Each pair from $A$ gives an independent triple with any outside point.

The first three Narayana polynomials are $N_1=x$, $N_2=x(1+x)$, and $N_3=x(1+3x+x^2)$. A triple meeting $A$ in $k$ points contributes

$$
\prod_{i=1}^7 N_{q_{B,i}}(x)=x^7(1+x)^{6-2k}(1+3x+x^2)^k.
$$

The weighted sum over $k$ gives the factorization above.

## Prior work and verification

Choe, Oxley, Sokal and Wagner used these same Fano intersection counts in Example 11.1 to disprove the half-plane property for its basis polynomial. The translation by $\mathbf 1+\mathbf 1_A$ carries that obstruction into Defant's Narayana sum. Searches for Defant's problem, generalized permutohedra, matroid base polytopes and Narayana sums found no earlier disproof. OpenAI Codex derived this transfer and wrote the Lean formalization. [Choe, Oxley, Sokal and Wagner](https://arxiv.org/abs/math/0202034)

The Lean statement uses symmetric exchange to describe exactly the lattice-point sets of integral generalized permutohedra. Defant explains this correspondence immediately after Question 6.1 and states it explicitly in Section 2.4 of the subsequent paper. The proof verifies exchange for the 28 points and checks the full polynomial identity and the nonreal-root argument. [Lattice-point characterization](https://arxiv.org/html/2611.13479#S2.SS4)

```sh
lake exe cache get
lake build conjectures.DefantNarayana.Solution
lake env leanchecker conjectures.DefantNarayana.Solution
```
