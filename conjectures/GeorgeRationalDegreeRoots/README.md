# Solution to George’s problem on the rational degree roots of graphs of a given order

Let $p,q$ be coprime positive integers. Some simple graph on $n$ vertices has
$-p/q$ as a root of its degree polynomial if and only if

$$
\begin{cases}
p+q\mid n, & n\text{ odd},\\
2(p+q)\mid n, & n\text{ even}.
\end{cases}
$$

For example, $-1$ occurs precisely at multiples of four. George’s Table 4.1 already lists this root at order eight. Two
disjoint edges and four isolated vertices give $D(x)=4+4x$.

Ian C. George asked which rational roots occur at each order and predicted
that $p+q$ divides $n$. He supplied constructions for odd orders and suggested
$p+q=n/2$ for even orders. The example above already gives $p+q=2$ at $n=8$.
The divisibility criterion describes all negative rational roots at every order.
[George, *On the Degree Polynomial of Graphs* (2023), §4.1, pp. 96–97](https://dalspaceb.library.dal.ca/server/api/core/bitstreams/b38bd694-b1b7-4993-a49f-b0d2dc04cc0b/content)

## Proof

Each vertex of degree $d$ contributes $x^d$ to $D(x)$. Hence
$D(1)=n$ and $D'(1)=2|E|$. If $D(-p/q)=0$, Gauss’s lemma gives a factorization
$D(x)=(qx+p)H(x)$ with $H\in\mathbb{Z}[x]$. At $x=1$ we get

$$n=(p+q)H(1),\qquad 2|E|=qH(1)+(p+q)H'(1).$$

Set $k=H(1)$. If $n$ is even and $p+q$ is odd, the first equation makes $k$
even. If $p+q$ is even, coprimality makes $q$ odd, and the second equation
makes $k$ even.

Conversely, put $k=n/(p+q)$. When $qk$ is even, pair $qk$ vertices into
disjoint edges and leave $pk$ vertices isolated. Their degree polynomial is
$pk+qkx$. When $qk$ is odd, the criterion forces $pk$ to be even. Pair $pk$
vertices and leave $qk$ vertices isolated. This graph has root $-q/p$, so its
complement has root $-p/q$, since $D_{\overline G}(x)=x^{n-1}D_G(1/x)$
for $x\ne0$ and $n\ge1$.

## Prior work and verification

George’s thesis already gives the complement identity and the existence of the
odd-order roots. Searches by author, the divisibility prediction, and graph
order found no previous classification. Brown and George’s subsequent paper
lists the determination of rational degree roots as future work on p. 181. [Brown and George, *On the Roots of Degree
Polynomials* (2025)](https://ajc.maths.uq.edu.au/pdf/92/ajc_v92_p164.pdf)

Run from the repository root.

```sh
# Run at the merge commit for PR #12.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The Lean proof constructs the matching and its complement. The declaration
`classification` states the criterion. The declaration `result` applies it to
George’s divisibility prediction and includes the reduced fraction $0/1$.
Codex derived the classification and wrote the formal proof.
