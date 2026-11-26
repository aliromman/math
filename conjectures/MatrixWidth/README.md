# The stationary width of the Matrix event graph

Suppose $k$ participants each add one vertex in a round. Each independently picks $d$ distinct parents uniformly from the current $u$ tips. The selected parents cease to be tips, and the $k$ new vertices become tips. For $k>d>1$, the chain has a stationary distribution, and every width $u\ge k$ has finite mean return time. This proves the conjecture of Jacob, Beer, Henze and Hartenstein. [Original paper, §§VIII.A–C](https://publikationen.bibliothek.kit.edu/1000129939/103560274)

The stationary width $U$ has an exact tail exponent:

$$
\lim_{m\to\infty}\frac{-\log\Pr(U\ge m)}{m\log m}
=\frac{d(k-1)}{k-d}.
$$

With three participants and two parents, for example, width can increase by at most one. This requires all three participants to select the same pair. Its probability is $\binom{u}{2}^{-2}$, of order $u^{-4}$. The tail exponent is four.

## Proof

Let $r$ be the number of distinct tips selected. A round changes the width by $j=k-r$. Choosing the union of the selected tips and then the subsets of that union gives

$$
\Pr(r)\le\frac{\binom ur 2^{rk}}{\binom ud^k}=O(u^{r-dk}).
$$

Put $h=k-d$ and $x=u-k$. Take $V(x)=((x+1)!)^\beta$ with $1<\beta<d(k-1)/h$. For an upward or level jump, the contribution to the expected ratio $V(x+j)/V(x)$ is at most a constant times $u^{-k(d-1)+(\beta-1)j}$. This tends to zero for every $0\le j\le h$. At a downward jump the ratio itself is at most $(x+1)^{-\beta}$. There are only finitely many jump sizes. Thus the full expected ratio tends to zero.

It follows that $PV\le V/2+D$ for some constant $D$, where $PV(x)$ is the expected value after one step from $x$. The time averages of the laws started at $x=0$ have a uniformly bounded $V$-moment. They have a pointwise convergent subsequence, whose limit has total mass one. Each width has only finitely many possible predecessors, so the limit is stationary. Both unit jumps are possible wherever their endpoints exist, so every state has positive stationary mass. Under a stationary law, a last-visit count bounds the mean return time to each state by the reciprocal of its mass.

Testing stationarity against $\min(V,M)$ and increasing $M$ gives $\mathbb E V\le 2D$ for every stationary law. It follows that $\Pr(U\ge k+x)\le 2D/((x+1)!)^\beta$, giving one side of the exponent. For the other, a jump of the maximum size $h$ occurs precisely when all $k$ participants choose the same $d$ parents. Its probability is $\binom ud^{1-k}$. For $m\ge k$, start at width $k$ and take $\lceil(m-k)/h\rceil$ such jumps. The final width is at least $m$. The product of their probabilities gives the matching exponent.

## Prior work and verification

The authors derived the one-step mean, variance and complete transition probabilities. They posed positive recurrence as an open problem. Bramas previously proved stability for a related process with a Poisson number of new arrivals each round. Searches by paper title, author, urn model and stationary width found no previous proof for this fixed-batch model or of its tail exponent. OpenAI Codex developed the argument and its Lean proof. [Bramas, §3](https://doi.org/10.4230/OASIcs.Tokenomics.2019.8)

The computation uses the original uniform subset space. A state with index $x$ represents physical width $k+x$. The theorem `resolution` proves the conjecture and `width_tail_rate` gives the limit in physical width.

```sh
lake exe cache get
lake build conjectures.MatrixWidth.Solution
lake env leanchecker conjectures.MatrixWidth.Solution
```
