# Proof of Yang, Yerger and Zhou’s Conjecture 2 on pebbling weights for pendant hypercubes

Attach a root $r$ by one edge to any vertex of the $m$-dimensional cube. If a pebble configuration $p$ cannot put a pebble on $r$, then

$$
\sum_{v\ne r}\frac{p(v)}{d(v,r)}\;\le\;\sum_{v\ne r}\frac{1}{d(v,r)}.
$$

This proves Conjecture 2 of Yang, Yerger and Zhou for every $m\ge2$. The authors used such weights in low dimensions and showed how the general result gives the ordinary cube pebbling number $2^n$. [Yang, Yerger and Zhou, *Lollipop and cubic weight functions for graph pebbling*, §2](https://doi.org/10.1007/s10878-024-01248-1)

## Proof

Identify a cube vertex with the set $X$ of coordinates in which it differs from the attachment. Its distance to $r$ is $|X|+1$. Write $W(p)$ for the left side of the inequality. For each coordinate $i$, push every available pair of pebbles across that coordinate toward the attachment. In the nearer face, each $X$ now contains

$$
p_i(X)=p(X)+\left\lfloor p(X\cup\{i\})/2\right\rfloor.
$$

Each push is an allowed move, so $p_i$ is still unsolvable. Also $p(\varnothing)\le1$, since two pebbles there could reach the root. Under this condition, summing over the faces gives

$$
(m+1)W(p)=\sum_{i=1}^m W(p_i)+\sum_X\left\lceil p(X)/2\right\rceil.
$$

Indeed, a pile on a nonempty $k$-set contributes $p(X)/(k+1)$ in $m-k$ nearer faces and $\lfloor p(X)/2\rfloor/k$ in the other $k$. At the attachment its contribution is $m p(\varnothing)$ from the faces and $p(\varnothing)$ from the ceiling.

Chung's odd two-pebble bound says that if $\sum_X\lceil p(X)/2\rceil>2^m$, two pebbles can reach the attachment. They could then reach the root. Thus this term is at most $2^m$. Apply induction to the $m$ nearer faces. For the all-ones configuration every folded face still has all ones, and the ceiling sum equals $2^m$. The displayed identity gives the claimed comparison, including the zero-dimensional base case. [Chung, *Pebbling in Hypercubes*, Theorem 2](https://doi.org/10.1137/0402041)

## Verification and attribution

```sh
# Run at the merge commit for PR #57.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The statement uses Mathlib graph distance, unrestricted finite pebble piles, and the original rule for a move. The proof constructs the moves in Chung’s two bounds and checks the facet identity. The axiom guard covers the final theorem. Searches for subsequent proofs using the conjecture, authors and reciprocal-distance weights found no earlier resolution. OpenAI Codex derived the facet argument and wrote the Lean proof.

Marshall Yang, Carl Yerger and Runtian Zhou, Lollipop and cubic weight functions for graph pebbling, §2, Conjecture 2. [Publication](https://link.springer.com/article/10.1007/s10878-024-01248-1)
