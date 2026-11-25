# A root rotation improves every proposed extremizer for the five-leaf tree

Dossou-Olory and Wagner proposed a sequence of binary trees that would contain the greatest possible limiting proportion of the five-leaf tree $A_5$. A single rotation at the root improves every sequence in their proposed family.

The root of $A_5$ joins a leaf to a balanced four-leaf tree. Five leaves of a host tree induce $A_5$ if their smallest connecting subtree has this shape after suppressing vertices with just one child. The inducibility $I_2(A_5)$ is the limit, as the number of leaves tends to infinity, of the maximum proportion of five-leaf subsets that induce $A_5$. [Czabarka, Székely and Wagner (2017)](https://arxiv.org/abs/1601.07149)

## The rotation

Write $(A,B)$ for the tree obtained by joining $A$ and $B$ to a new root. Take three trees $A,B,C$ with $a,b,c$ leaves, respectively. Rotate $((A,B),C)$ to $(A,(B,C))$. A five-leaf subset can change its contribution only if it uses leaves in all three branches. The rotation creates copies with one leaf in $A$, two in $B$, and two in $C$. It removes copies with two leaves in $A$, two in $B$, and one in $C$. The net gain is

$$
a\binom b2\binom c2-c\binom a2\binom b2
=\frac{abc(b-1)(c-a)}4.
$$

This gain is positive whenever $b\ge 2$ and $c>a$. If the three leaf counts have limiting proportions $\alpha,\beta,\gamma>0$ with $\gamma>\alpha$, dividing by the total number of five-leaf subsets gives a positive limiting gain of $30\alpha\beta^2\gamma(\gamma-\alpha)$.

## The proposed sequence

An even tree on $m$ leaves splits into two even trees of sizes $\lfloor m/2\rfloor$ and $\lceil m/2\rceil$. Dossou-Olory and Wagner attach four even trees to a four-leaf caterpillar, in the shape $(T_1,(T_2,(T_3,T_4)))$. Each $T_i$ has $\lfloor x_i n\rfloor$ leaves for a fixed $x_i>0$, and the four proportions sum to one. The authors conjectured that some choice of proportions attains the inducibility. [Original conjecture, p. 5, and construction, Figure 6 and §4](https://arxiv.org/pdf/1811.12010#page=5) · [Journal publication](https://doi.org/10.23638/DMTCS-21-4-13)

Choose the root branch with the smaller limiting proportion and split it into its two children $A,B$. Call the opposite branch $C$. Both children have positive limiting proportions. The proportion of $A$ is strictly smaller than that of its parent, so it is strictly smaller than that of $C$. The rotation therefore raises the limiting density. It also works when the two root branches have equal limiting proportions.

The original authors proved a lower bound of about $0.2470715$. Brosch and Puges later gave an upper bound of $0.2471566$, rounded up. The exact inducibility remains open. Searches for the proposed sequence, improved lower bounds, and rotations found no earlier refutation of its optimality. [Brosch and Puges, Table 3](https://doi.org/10.1007/s10107-025-02305-1)

## Verification

`Statement.lean` defines finite binary trees, the leaf-induced copy counts from equations (5) and (6) of the original paper, the four branches, and the limit of the maximum density. `Solution.lean` proves the finite rotation identity and the negation of the conjecture. OpenAI Codex derived the argument and formalized it in Lean.

From the repository root, run

```sh
lake exe cache get
lake build conjectures.WagnerTreeInducibility.Solution
lake env leanchecker conjectures.WagnerTreeInducibility.Solution
```
