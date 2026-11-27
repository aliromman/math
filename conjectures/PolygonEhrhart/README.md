# Solution to Lundström and Saud Maia Leite’s Question 6.4 on Ehrhart nonnegativity of order polytopes of polygon face lattices

Let $L(t)$ count the lattice points in the $t$-th dilate of the order polytope of the face lattice of a 13-gon. Its linear coefficient is

$$
[t]L(t)=-\frac{298495711}{35302608}.
$$

This gives a negative answer to Lundström and Saud Maia Leite’s question about polygons. Their paper proves coefficient positivity for the crown poset of vertices and edges. The full face lattice adds the empty face and the polygon itself. The authors also found a negative coefficient in the **order polynomial** of the 7-gon face lattice. The Ehrhart polynomial counts maps to $`\{0,\ldots,t\}`$ and equals the order polynomial evaluated at $t+1$. The paper explicitly asks whether the coefficients after that translation remain nonnegative. [Published paper, Question 6.4](https://www.sciencedirect.com/science/article/pii/S0195669825001969) · [Authors’ revised preprint, Question 6.5, p. 33](https://arxiv.org/pdf/2504.05123#page=33)

## Counting the lattice points

A lattice point assigns a height in $`\{0,\ldots,t\}`$ to each face. Heights increase weakly under inclusion. Fix the bottom and top heights. If their difference is $s-1$, subtracting the bottom height gives $s$ available heights for each vertex and edge. An edge whose endpoints have heights $`i,j\in\{0,\ldots,s-1\}`$ has exactly $s-\max(i,j)$ possible heights.

Let $K_s$ be the $s\times s$ matrix with entries $s-\max(i,j)$. Multiplication sums over successive vertex heights. Taking the trace closes the cycle. There are $t+2-s$ choices of bottom height, so

```math
L(t)=\sum_{s=1}^{t+1}(t+2-s)\,\mathop{\mathrm{tr}}(K_s^{13}).
```

For example, this gives $L(0)=1$, $L(1)=271445$, and $L(2)=1385949918$. The polytope has dimension 28, one coordinate per face. Differentiating the interpolation formula at zero gives

$$
L'(0)=\sum_{j=1}^{28}\frac{(-1)^{j+1}}{j}\binom{28}{j}\bigl(L(j)-L(0)\bigr)
=-\frac{298495711}{35302608}.
$$

The counts satisfy $1\le L(t)\le (t+1)^{28}$ because the all-zero assignment is valid. These bounds force every polynomial that gives these counts to have degree at most 28.

## Verification and attribution

The Lean proof starts from the face-incidence inequalities. It proves the transfer identity, computes all 29 sample counts in the kernel, and checks the interpolation functional on the monomial basis. Each multiplication by the transfer matrix takes one prefix sum and one suffix sum, since its entry counts the heights above both endpoints.

```sh
# Run at the merge commit for PR #93.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Searches for the published question, polygon face lattices, Ehrhart positivity and the 13-gon coefficient located no prior counterexample. Recent work proving real-rootedness for the $h^*$-polynomial of the crown addresses a different polynomial. OpenAI Codex found the counterexample, derived the transfer calculation and formalized the proof. [Real-rootedness paper](https://arxiv.org/abs/2610.40496)
