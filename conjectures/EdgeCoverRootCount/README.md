# Minimum degree forces distinct edge-cover roots

If every vertex of a finite simple graph has at least $d$ incident edges, its edge-cover polynomial has at least $d$ distinct complex roots. For example, the triangle has minimum degree two and edge-cover polynomial $3x^2+x^3$. Its two roots are $0$ and $-3$.

Saeid Alikhani states this bound as Conjecture 5 in *Graphs Whose Certain Polynomials Have Few Distinct Roots* and attributes it to Saieed Akbari and Mohammad Reza Oboudi. The bound converts a local incidence condition into a lower bound on the number of different zeros of a graph polynomial. [Alikhani, Conjecture 5](https://doi.org/10.1155/2013/195818) · [Akbari and Oboudi, *On the edge cover polynomial of a graph*](https://doi.org/10.1016/j.ejc.2012.05.005)

## Proof

Let $m$ be the number of edges and $d$ the minimum degree. The case $d=0$ is immediate. An edge cover is a set of edges that meets every vertex. Write $P(x)$ for the sum of $x^{|S|}$ over all edge covers and $B(x)$ for the same sum over all other edge sets. Then

$$
P(x)+B(x)=(1+x)^m,\qquad \deg B\le m-d.
$$

Akbari and Oboudi give this identity and degree bound in their proof of Theorem 19. A set counted by $B$ omits all the edges at some vertex. The full edge set is a cover and the empty set is not. Thus $P$ has degree $m$ and $B$ is nonzero.

Differentiate the identity and form

$$
Q(x)=(1+x)P'(x)-mP(x)=mB(x)-(1+x)B'(x).
$$

If $B$ has degree $b<m$, the leading coefficient of $Q$ is $m-b$ times that of $B$. In particular, $Q$ is nonzero and has degree at most $m-d$. Each root of $P$ of multiplicity $r$ contributes at least $r-1$ to the degree of $Q$. If $P$ has $t$ distinct complex roots, then

$$
m-t\le \deg Q\le m-d,
$$

which proves $t\ge d$.

## Verification and prior work

The Lean statement counts all edge covers of a finite simple graph and counts its complex roots without multiplicity. From the repository root, run

```sh
lake exe cache get
python3 scripts/verify.py
```

Searches for the authors, the conjecture, and lower bounds on the number of distinct edge-cover roots found no earlier proof. Akbari and Oboudi used the degree bound to study real roots with multiplicity. The derivative combination above counts distinct complex roots. [Akbari and Oboudi, proof of Theorem 19](https://janos.cs.technion.ac.il/COURSES/236603-11/oboudi.pdf#page=17) Bencs, Csikvári and Regts bounded the locations of all edge-cover roots. OpenAI Codex derived the derivative argument and wrote the Lean proof. [Bencs, Csikvári and Regts](https://doi.org/10.37236/10185)
