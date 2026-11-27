# Disproof of Leander and Linusson’s Conjecture 2 on path correlation in randomly oriented fixed-edge graphs

Choose three of the six edges on four vertices uniformly, then orient each chosen edge by an independent fair coin. Let $A$ be the event that there is a directed path from $s$ to $a$, and $B$ the event that there is one from $t$ to $b$, where the four vertices are distinct. Then

$$
\Pr(A)=\Pr(B)=\frac7{20},\qquad
\Pr(A\cap B)=\frac1{10},\qquad
\mathop{\mathrm{Cov}}(\mathbf1_A,\mathbf1_B)=-\frac9{400}.
$$

This disproves Conjecture 2 of Madeleine Leander and Svante Linusson. They conjectured positive correlation for every vertex count $n$ and edge count $m$ in the uniformly oriented fixed-edge model. Their statement uses the complementary events that the paths are absent. Taking both complements preserves covariance. They proved positivity for every fixed positive edge density and sufficiently large $n$. [*Correlation of Paths Between Distinct Vertices in a Randomly Oriented Graph*, Math. Scand. 116 (2015), pp. 287–300, especially p. 295](https://www.mscand.dk/article/download/21163/18655/48247)

For each fixed $m\ge1$, we obtain a negative leading term when the number of vertices grows.

$$
\lim_{n\to\infty} n^4\mathop{\mathrm{Cov}}(\mathbf1_A,\mathbf1_B)=-m.
$$

More generally, the probability of $r$ specified directed connections on $2r$ distinct vertices, multiplied by $n^{2r}$, tends to the falling factorial $m(m-1)\cdots(m-r+1)$. The limit is zero when $r>m$.

## Four vertices

There are $`\binom63\,2^3=160`$ oriented outcomes. Forty contain the arc $s\to a$. Each of the two possible paths of length two occurs in eight outcomes, one of which also has the direct arc. The two paths of length three each occur once. The total is $40+2(8-1)+2=56$.

For the joint event, classify an outcome by which requested paths are direct arcs.

| Direct arcs present | Outcomes |
| --- | ---: |
| Both | 8 |
| Only $s\to a$ | 3 |
| Only $t\to b$ | 3 |
| Neither | 2 |

With only $s\to a$ direct, the second path can go through $s$, through $a$, or through $s,a$ in that order. With neither direct, the only possibilities are the chains $s\to t\to a\to b$ and $t\to s\to b\to a$. The joint event therefore occurs 16 times.

## The sparse limit

List the tails and heads of the $m$ directed edges in $2m$ slots. Each oriented simple graph occurs in exactly $m!$ orders. Of the $n^{2m}$ unrestricted lists, all but $O_m(n^{2m-1})$ have distinct entries. A list with distinct entries is a matching. The $r$ desired paths then require $r$ distinct ordered edge slots, each containing its prescribed tail and head. There are $(m)_r$ ways to choose these slots.

If $m>r$, each choice leaves $2m-2r$ free entries. A repeated value removes at least one free choice. The same estimate bounds the contribution from all possible longer paths. Indeed, both endpoints of each path must occur in the list. Fix one occurrence of each of the $2r$ prescribed vertices. If any two slots agree, at least one lies outside these fixed occurrences. Once its partner is specified, its value is determined. For fixed $m,r$ the number of choices of slot positions is bounded independently of $n$.

The favorable count is consequently $`(m)_r n^{2m-2r}+O_{m,r}(n^{2m-2r-1})`$. When $m=r$, all slots are needed for distinct prescribed vertices and the count is exactly $m!$. When $m<r$, there are too few slots. Taking $r=1,2$ gives the covariance limit since $(m)_2-m^2=-m$.

## Verification and attribution

Run these commands from the repository root.

```sh
# Run at the merge commit for PR #94.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Lean checks the uniform edge-ordering multiplicity, the four-vertex count, the general disjoint-path limit, and the covariance limit. The source statement is in `Statement.lean`. Searches by title, authors, conjecture number, fixed-edge covariance, and sparse directed paths found no earlier disproof. The original authors also reported exact computations for the independent-edge model in their separate Conjecture 1. AI developed this counterexample, the sparse-limit argument, and the Lean proofs.

Leander and Linusson, “Correlation of Paths Between Distinct Vertices in a Randomly Oriented Graph,” Mathematica Scandinavica 116 (2015), 287–300, Conjecture 2, p. 295, DOI 10.7146/math.scand.a-21163. This is the uniform fixed-edge model. [Publication](https://www.mscand.dk/article/view/21163)
