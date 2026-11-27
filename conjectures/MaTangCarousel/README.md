# Disproof of Ma and Tang’s Conjecture 5.2 on even-cycle homomorphism densities in tournaments

Split a tournament into three equal groups. Order the players from first to last within each group, with the earlier player beating the later one. Every player in the first group beats every player in the second, the second beats the third, and the third beats the first.

The directed triangle density is exactly $1/9$, for every positive group size. As the groups grow, the directed six-cycle density tends to

$$
\frac{5}{486}=0.0102880658\ldots
$$

Ma and Tang’s Conjecture 5.2 predicts at least $20215/1889568=0.0106982125\ldots$ at this triangle density. The gap $775/1889568$ persists as the order tends to infinity. [Original paper, Conjecture 5.2](https://arxiv.org/pdf/2011.14142#page=15)

## Counting the cycles

The density $t(C_\ell,T)$ is the chance that $\ell$ independently and uniformly chosen vertices, in their sampled order, follow the edges of a directed cycle. The first and last sample also have to be connected in the prescribed direction. The definition allows repeated vertices. A tournament consists of one directed edge between each pair of distinct vertices.

A step of a directed cycle either advances one group around the triangle or stays in the same group and moves upwards in rank. A closed cycle must advance a positive multiple of three times. There are three choices of the starting group. A triangle must advance at every step, giving probability $3/3^3=1/9$.

A six-cycle advances six times or three times. With six advances there is no rank restriction. With three advances, select three of the six positions as the steps that stay in their group. In the limit the six ranks are distinct, and all their relative orders are equally likely.

| Three positions that stay in their group | Number of choices | Probability of the required rank order |
| --- | ---: | ---: |
| Three consecutive positions | 6 | $1/24$ |
| Two consecutive and one isolated | 12 | $1/12$ |
| Alternating positions | 2 | $1/8$ |

The first row requires four ranks in order. The second requires three in order and one independent comparison. The third requires three independent comparisons. Thus

$$
t(C_6,T)\;\longrightarrow\;
\frac{3}{3^6}\left(1+\frac{6}{24}+\frac{12}{12}+\frac{2}{8}\right)=\frac{5}{486}.
$$

For finite groups, ties can only remove strict comparisons. The same fraction is an upper bound for every group size.

## Comparing the proposed extremizer

The authors propose a transitive sequence of groups whose internal tournaments are carousels. At triangle density $1/9$ the construction has two groups of masses $z$ and $1-z$, with $z^3+(1-z)^3=8/9$, so $z(1-z)=1/27$. Their equation (11) gives the six-cycle density inside a carousel as $\alpha_6=1/64-2\sum_{k\ge0}((2k+1)\pi)^{-6}=13/960$. The prediction is therefore

$$
\alpha_6\bigl(z^6+(1-z)^6\bigr)
=\frac{13}{960}\left[\left(\frac89\right)^2-2\left(\frac1{27}\right)^3\right]
=\frac{20215}{1889568}.
$$

This gives a counterexample already at the smallest cycle length in Conjecture 5.2. The exact minimum at triangle density $1/9$ remains open.

## Source and verification

Jie Ma and Tianyun Tang published the conjecture in *Combinatorial Theory* 2(3), article 6 (2022). They had already shown that their proposed bound is attained by their carousel construction. Searches for Conjecture 5.2, the six-cycle minimization problem, the three-part construction and its exact density found no prior counterexample. OpenAI Codex found the example and formalized the proof. [Journal article](https://escholarship.org/uc/item/2rm2x1nm) · [Conjecture](Statement.lean) · [Finite counts](Orders.lean) · [Carousel constant](Constant.lean) · [Disproof and limit](Solution.lean)

~~~sh
# Run at the merge commit for PR #89.
python3 scripts/verify.py --base HEAD^ --fetch-cache
~~~
