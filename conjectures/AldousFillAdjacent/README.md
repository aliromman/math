# Undoing a card swap doubles the first correction to the mean hitting time

Place $m$ cards on a circle. At each step, choose uniformly among a hold and the $m$ swaps of neighboring cards. Start with a uniform random deck and choose an independent uniform target. The mean time $\tau_m$ to reach the target satisfies

$$
\frac{\tau_m}{m!}=1+\frac{2}{m}+O(m^{-2}).
$$

Aldous and Fill predicted a coefficient of $1$ from their local transience heuristic. A hold returns the deck to its starting state in one step. Making the same choice twice returns it in two steps. For $m\ge3$, each return has probability exactly $1/(m+1)$. Both affect the coefficient. [Aldous and Fill, *Reversible Markov Chains and Random Walks on Graphs*, Example 7.22, pp. 255–256](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch7.S2.html)

## A finite disproof

Fix the identity deck as target by symmetry. Write $N=m!$, let $P$ be the transition operator, and put $L=I-P$. Let $\delta$ be the indicator of the identity and $p_j=(P^j\delta)(1)$ the probability of returning in $j$ steps. Use the inner product $\langle f,g\rangle=\sum_x f(x)g(x)$.

Let $h(x)$ be the mean time to the identity from $x$. It has $h(1)=0$ and $Lh(x)=1$ off the identity. Summing gives $Lh=1-N\delta$. Each move is an involution, so $P$ is symmetric. The energy $E(f)=\langle f,Lf\rangle$ is half the sum, over starting decks, of the expected squared change in $f$ in one step.

Take $q=\delta+P\delta$. Then $Lq=\delta-P^2\delta$, and expanding $E(h+Nq)\ge0$ gives

$$
\frac{\tau_m}{N}\ge 1+p_1+p_2+p_3-\frac4N
\ge 1+\frac{2}{m+1}-\frac4N.
$$

For $m\ge5$ this exceeds $1+1/m$ by at least $1/(4m)$.

## Bounding all later returns

Every permutation is a product of at most $m$ transpositions, and each can be written using at most $2m$ adjacent swaps. Telescoping along these paths and using Cauchy–Schwarz gives $\langle f,f\rangle\le B E(f)$ for mean-zero $f$, where $B=(2m^2)^2(m+1)$.

Put $u=(\tau_m-h)/N$. It has mean zero, $Lu=\delta-1/N$ and $E(u)=\tau_m/N$. Symmetry gives $E(f)-E(Pf)=\langle Lf,Lf+PLf\rangle$. Apply this to $f=P^ju$ and sum over $0\le j<r$. The leftover energy $E(P^ru)$ lies between zero and $B\langle LP^ru,LP^ru\rangle$ by Cauchy–Schwarz and the preceding bound. Consequently,

$$
0\le \frac{\tau_m}{N}-\sum_{j=0}^{2r-1}\left(p_j-\frac1N\right)\le B p_{2r}.
$$

Consider a sequence of $k<m$ choices that returns the deck to its initial state. Some circle edge is unused. Cutting there turns the remaining edges into a path. If a swap edge occurs exactly once, a card crosses the cut at that edge and cannot return. Thus at most $\lfloor k/2\rfloor$ distinct edges occur. For fixed $k$, there are $O_k(m^{\lfloor k/2\rfloor})$ such sequences among $(m+1)^k$ choices. Hence $p_k=O_k(m^{-\lceil k/2\rceil})$.

Choose $r=7$. Returns at steps $3$ through $13$ contribute $O(m^{-2})$, and $B p_{14}=O(m^5 m^{-7})$. The first three returns give $1+2/(m+1)$, which proves the formula.

## Verification and attribution

Run these commands from the repository root.

```sh
lake build conjectures.AldousFillAdjacent.Solution
lake env leanchecker conjectures.AldousFillAdjacent.Solution
```

Example 7.21 of the same source treats swaps of arbitrary pairs and credits Flatto, Odlyzko, and Wales. Searches for stationary hitting times of cyclic adjacent-transposition shuffles, the modified bubble-sort graph and its Kirchhoff index found no earlier correction of Example 7.22. OpenAI Codex found the return obstruction and the corrected expansion, and wrote the Lean proofs.
