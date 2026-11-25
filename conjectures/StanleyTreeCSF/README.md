# Stanley's tree isomorphism question

Exchanging two rooted branches cannot give a counterexample by the argument below. A search at three attachment sites separated 111,144 trees on 49 to 85 vertices. Stanley's question remains open. This research note gives a partial argument and a reproducible finite search. It has no Lean proof or claim of priority.

Stanley asked whether the chromatic symmetric function distinguishes finite unrooted trees up to graph isomorphism. For a tree $T$, this function is $X_T=\sum_\kappa\prod_{v\in V(T)}x_{\kappa(v)}$, summed over all proper colorings by positive integers. The question is whether $X_T=X_{T'}$ implies $T\cong T'$. Heil and Ji checked every tree through 29 vertices. Orellana and Tomba reported the general question open in November 2026. [Stanley, 1995, p. 170](https://math.mit.edu/~rstan/pubs/pubfiles/100.pdf) · [Heil and Ji](https://arxiv.org/abs/1801.07363) · [Orellana and Tomba](https://arxiv.org/abs/2611.18940)

## Two attachment sites

Choose distinct vertices $u,v$ of a tree $H$. Identify them with the roots of trees $A,B$, respectively, to obtain $T$. Exchange the attachments to obtain $T'$. The distance between $u$ and $v$ and the degrees of all the roots are arbitrary.

Give each vertex spin $+$ or $-$. Let $Z$ sum $z^{n_+}a^b$ over all spin assignments, where $n_+$ counts plus vertices and $b$ counts edges with opposite spins. Write $P_S^+$ and $P_S^-$ for the two sums with the root of $S$ fixed. The two-spin polynomial $Z$ is determined by $X_T$. In fact, expand each edge weight as $a+(1-a)\mathbf 1_{\rm equal}$. Choosing the second term on an edge set $F$ gives

$$
a^{|E|-|F|}(1-a)^{|F|}\prod_{C}(1+z^{|C|}),
$$

where $C$ runs through the components of $(V,F)$. Stanley's power-sum formula counts the edge sets with each list of component sizes, since on a tree $|F|=|V|-\#C$. [Stanley, Theorem 2.5](https://math.mit.edu/~rstan/pubs/pubfiles/100.pdf)

Only assignments with opposite spins at $u,v$ contribute to the difference. Both attachments then count the plus site one extra time before identification. This gives

$$
z\bigl(Z(T)-Z(T')\bigr)
=\bigl(P_{(H,u)}^+-P_{(H,v)}^+\bigr)
 \bigl(P_A^+P_B^- - P_A^-P_B^+\bigr).
$$

The first factor vanishes precisely when an automorphism of $H$ sends $u$ to $v$. This follows from the theorem that $P_S^+$ determines the rooted tree $S$. For the second factor, it suffices that $P_S^+/P_S^-$ is a reduced fraction. Here is the factorization. For each child subtree $D$, put $F_D=P_D^++aP_D^-$ and $F_D^*=z^{|D|}F_D(1/z)$. Complementing every spin gives

$$
P_S^+=z\prod_D F_D, \qquad P_S^-=\prod_D F_D^*.
$$

In $\mathbb Z[a][z]$, each $F_D$ is monic, has constant term $a$, and reduces to $z^{|D|}$ modulo $a$. Eisenstein's criterion makes it irreducible. Its reciprocal is irreducible too, with constant term 1 and leading coefficient $a$. Thus no numerator factor divides the denominator. The denominator has constant term 1, so equality of the fractions forces equality of the plus polynomials and hence rooted isomorphism. The rooted-tree theorem and its Eisenstein argument appear in Law's thesis, Chapter 4, credited jointly to Alex Scott. [Law, Theorem 4.8](https://doi.org/10.5287/ora-xq7ybbmz9)

Thus equal $X$ forces either $A$ and $B$ to be rooted-isomorphic or $u$ and $v$ to be equivalent in $H$. In the latter case a tree automorphism can interchange them. Root $H$ at its center, subdividing a central edge if necessary. At the last common ancestor of the two vertices, exchange their two child subtrees using the isomorphism in one direction and its inverse in the other. In either case $T\cong T'$. Krasikov previously characterized these two possibilities for an interchange that gives isomorphic trees. [Krasikov, 1991](https://doi.org/10.1007/BF01788141)

## Three attachment sites

Choose three pairwise nonisomorphic rooted trees $L_1,L_2,L_3$ of order $k$. Join each root $r_i$ by an edge to a new vertex to form $H$. At each $r_i$ in $H$, identify that vertex with $r_{\sigma(i)}$ in a fresh copy of $H$, for each of the six permutations $\sigma$. All trees have $12k+1$ vertices. The three attachment sites have equal-sized branches, so a single cut of the host that separates the sites sees the same split sizes. Such agreements motivate the test. Earlier work constructed trees that agree for arbitrarily many initial cut counts. [Aliste-Prieto, de Mier and Zamora](https://doi.org/10.1016/j.disc.2020.112255)

| Vertices | Trees tested | Distinct $Z(z=3,a=2)$ | Distinct $X(2,3,5,0,\ldots)$ |
|------:|------:|------:|------:|
| 49 | 24 | 24 | 24 |
| 61 | 504 | 504 | 504 |
| 73 | 6,840 | 6,840 | 6,840 |
| 85 | 103,776 | 103,776 | 103,776 |

Each column independently separates every tree tested at each order by exact integer evaluation. For a concrete close pair take the four-vertex star rooted at its center, the four-vertex path rooted at an inner vertex, and the star rooted at a leaf, in that order. Compare the two opposite 3-cycles. Every partition count agrees for zero through three deleted edges. With four edges deleted, the component orders $(33,11,3,1,1)$ occur **208** and **207** times.

From the repository root, run the following command with Python 3.9 or later. It also checks the 49-vertex pair by enumerating cuts directly. One run used 1.55 CPU seconds. OpenAI Codex developed the argument and implemented the search.

```sh
python3 conjectures/StanleyTreeCSF/replay.py
```
