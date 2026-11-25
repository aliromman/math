# Every finite set of positive integers is a bipartite score set

Let two teams play across the team boundary. A win gives 2 points, a missing game gives each player 1, and a loss gives 0. **Every finite nonempty set of positive integers occurs as the set of all player scores.** If the largest score is $M$, we can give every player on the right that score, using at most $\lfloor M/2\rfloor+1$ players on the right. This bound is sharp.

Pirzada, Naikoo and Chishti posed the existence question in 2006. In their graph, each pair across the two parts has one directed edge or no edge. The score is the size of the opposite part plus outdegree minus indegree. Their paper established the result for several classes, including sets of size at most three. The construction below covers every finite nonempty set of positive scores. [Original paper, Conjecture 2.1, p. 44](https://emis.de/ft/50074)

## Proof

Give the right team $n$ players. A left player who scores $a$ gives the right team $2n-a$ points. To make every right score $M$, we need left players whose contributions add to $nM$. Once we have them, deal the points cyclically to the $n$ right players, continuing from the last position after each left player. Each left player contributes at most $2n$, so each pair receives 0, 1, or 2 points. The total of $nM$ gives every right player exactly $M$.

If $M$ is odd, take $n=(M+1)/2$. Include each requested score $a<M$ once. Its contribution is $M+1-a$. These contributions are distinct members of $\{2,\ldots,M\}$, so their sum is at most $nM$. Fill the remaining total with contributions of 1. Each comes from a left player with score $M$.

If $M=2h$, form the set $D$ of deficits $M-a$ over the requested scores $a<M$. Let $k$ be the number of missing deficits in $\{1,\ldots,M-1\}$, and let $T$ be their sum.

- If $T<h$, take $n=h$ and include one left player for every deficit in $D$. This leaves $h+T$ points to allocate. The integer $h+T$ lies below $M$ and exceeds the sum of all missing deficits. It therefore belongs to $D$. Use that deficit a second time.
- If $T\ge h$, take $n=h+1$. Each initial player now contributes $d+2$ for some $d\in D$. The remaining total is $R=T+2k+2-h\ge 2k+2$. A player with score $M$ contributes 2, so we can fill an even remainder. If $R$ is odd, some $d\in D$ is odd. The least such $d$ is at most $2k+1$, since every smaller positive odd number is missing. Thus $d+2\le 2k+3\le R$. Use this contribution once and fill the even balance with twos.

For sharpness, request the singleton $\{M\}$. If $2n\le M$, every left player must take every available point to reach $M$, leaving the right players with score zero. Thus $n\ge\lfloor M/2\rfloor+1$.

## Verification and attribution

`Statement.lean` defines the graph, the scores, and the original conjecture. `Allocation.lean` proves the cyclic allocation works. `Solution.lean` proves the existence theorem and the sharp bound. The project pins Lean 4.36.0 and Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Run these commands from the repository root.

```sh
lake exe cache get
lake build conjectures.BipartiteScoreSets.Solution
lake env leanchecker conjectures.BipartiteScoreSets.Solution
```

The priority search covered the original authors, their multipartite extension, later work on score sets, and public proof catalogues. We found no earlier general resolution. The established theorem on tournament outdegrees uses a different scoring rule. AI agents developed the construction, wrote the Lean proof, and independently checked it. [Original preprint](https://arxiv.org/abs/math/0609135) · [Multipartite extension](https://doi.org/10.1080/09728600.2006.12088811)
