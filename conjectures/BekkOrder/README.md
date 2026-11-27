# Disproof of Berend, Ernst, Kontorovich and Kumar’s Conjecture 5.2 as stated and proof of the corrected interior interval tiling

Fix an even integer $2\le k<n$. Among $n$ Bernoulli variables of common mean $p$ that are independent in every group of $k$, which joint laws maximize the probability that all variables equal one? As $p$ increases from zero to one, the nondegenerate optimal bases occur in lexicographic order. Each occupies one interval. Their closures cover $[0,1]$, with consecutive intervals meeting at a single bias.

The endpoint counterexample disproves Conjecture 5.2 of Berend, Ernst, Kontorovich and Kumar as stated. The corrected interior interval tiling holds for every even $k$ in the stated range. With the paper’s literal definition, a basis can be feasible again at $p=1$ after its interval ends. For $n=3$, $k=2$, the basis $\{0,1,3\}$ has weights $(1-p)(1-2p),3p(1-p),p^2$. Its feasibility set is $[0,1/2]\cup\{1\}$. Taking the closure of each nondegenerate *interior* feasibility interval gives precisely the proposed tiling. [Original paper, §5 and Conjecture 5.2](https://link.springer.com/article/10.1007/s10959-026-01487-4#Sec14)

## Why the order is forced

Symmetrize the joint law and let $X$ count its ones. The first $k$ moments of $X$ agree with those of a binomial variable of parameters $n,p$. Conversely, use a uniform binary word conditional on $X$ to recover a joint law. The source identifies the dual-feasible bases as $n$ together with $k/2$ disjoint adjacent pairs. On such a basis the moment equations determine the weights uniquely by polynomial interpolation. Nonnegative weights certify an optimum by the source’s duality theorem.

Suppose basis $A$ precedes $B$ lexicographically. Write $a_i,a_i+1$ for the first pair of $A$ on which they differ. Put $c=a_i+1$ and form

$$
h(x)=(n-x)\prod_{j\ne i}(x-a_j)(x-a_j-1).
$$

On the integer grid $0,\ldots,n$ every factor pair is nonnegative. At the nodes of $A$, the polynomial $(x-c)h(x)$ vanishes except at $a_i$, where it is negative. At the nodes of $B$ the polynomial is nonnegative. Since its degree is $k$, both statements transfer to its binomial expectation at a bias where the respective basis is feasible.

For $0<p<q<1$, the ratio of the binomial probability at $q$ to that at $p$ is $C r^x$ with $r>1$. If the expectation of $(x-c)h(x)$ at $p$ is nonnegative, then its expectation at $q$ is strictly positive. Subtract the multiple $C r^c$ of the earlier expectation. Every summand has the sign of $(r^x-r^c)(x-c)h(x)$, and at least one is positive. Thus $B$ cannot be feasible before $A$. Applying this test at both ends of each adjacent pair also shows that its two weights remain nonnegative between any two feasible parameters. This proves that each interior feasibility set is an interval.

For coverage, minimize the basic mass at $n$ over the finite set of bases. The polynomial $Q$ with simple roots at its paired nodes and $Q(n)=1$ is nonnegative on the grid. Its expectation is this mass. If another basic weight at $u$ is negative, add a positive multiple of the cardinal interpolation polynomial at $u$ until the first new grid point reaches zero. The expected value decreases. The new polynomial has $k$ distinct grid zeros and value one at $n$. Its simple roots come in adjacent pairs since the sign between successive roots alternates. These zeros give a new basis, contradicting minimality. At each interior bias at least one basis is therefore feasible. A basis with no interval of positive length can cover at most one interior point. There are only finitely many such points, so the closures of the nondegenerate intervals cover the whole unit interval.

## Sources and verification

The authors computed many cases through $k=10$. Roy Hermann later proved the reflection of exceptional points, Conjecture 5.11. His proof explicitly leaves ordering and connectedness open. Searches for the original conjecture, the authors, and subsequent work on optimal supports found no earlier proof of the corrected interior ordering and tiling. OpenAI Codex developed the sign test, the coverage proof and the Lean formalization. [Hermann’s reflection theorem](https://arxiv.org/html/2609.25595v1)

```sh
# Run at the merge commit for PR #96.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The final theorem proves the ordered intervals with disjoint interiors, their coverage, and the failure of the literal endpoint convention.
