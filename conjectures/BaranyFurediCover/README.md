# The sharp lattice-square bound in Bárány and Füredi’s covering-radius conjecture

The square with vertices $(0,0),(2,1),(1,3),(-1,2)$ has area 5 and lattice covering radius $3/5$. Its longest line of lattice points contains three points, so its lattice diameter is 2. Thus

$$
\frac{\operatorname{area}(P)\,\mu(P)}{\ell(P)}=\frac32.
$$

This is the largest possible ratio for a square with lattice vertices. There are also squares of arbitrarily large lattice diameter that exceed the proposed constant $(1+\sqrt2)/2$.

## The original comparison

Bárány and Füredi define $\ell(P)$ as the greatest number of lattice points on a line in $P$, less one. The covering radius $\mu(P)$ is the least scale at which integer translates of the scaled polygon cover the plane. After equation (6), the authors compare $\operatorname{area}(P)\mu(P)$ with $\ell(P)$ and propose the factor $(1+\sqrt2)/2$. Their own example $Q^6(t)$ already yields $16/13>(1+\sqrt2)/2$ at $t=1$. Their paper gives both numbers. The results proved here determine the sharp constant for all lattice squares and show that the proposed factor still fails at unbounded lattice diameter. [Bárány and Füredi, *On the lattice diameter of a convex polygon*, Discrete Mathematics 241 (2001), pp. 41–50, §3](https://www.renyi.hu/~barany/cikkek/84.pdf#page=5)

## The three exact quantities

Translate the square and apply a symmetry of the integer grid. Its side vectors can be written as $(a,b)$ and $(-b,a)$ with integers $a\ge b\ge0$ and $a>0$. Put $D=a^2+b^2$. Then

$$
\operatorname{area}(P)=D,\qquad
\mu(P)=\frac{a+b}{D},\qquad
\ell(P)=a+\left\lfloor\frac{b^2}{a}\right\rfloor.
$$

The first formula is the determinant. To see the second, center the square at the origin. In the two perpendicular directions its defining inequalities are $|ax+by|\le D/2$ and $|ay-bx|\le D/2$. Round each coordinate of a target point to the nearest integer. Both errors in these inequalities are at most $(a+b)/2$. At $(1/2,1/2)$, for any choice of lattice point, the two coordinate errors both have magnitude at least $1/2$. One of the two linear forms adds their magnitudes with coefficients $a,b$, which proves equality.

For any nonzero lattice direction $(i,j)$, at least one of $|ai+bj|$ and $|aj-bi|$ is at least $a$. A lattice string of length $k$ therefore satisfies $ka\le D$. On the horizontal line $y=b$, the square contains the integer points from $x=-\lfloor b^2/a\rfloor$ to $x=a$. This gives the third formula.

To bound the ratio, set $m=\lfloor b^2/a\rfloor$. We need $2(a+b)\le3(a+m)$. For $a\ge4$, the opposite inequality would give $a(2b-a)\ge3am+a>3b^2-2a$. But $a^2-2ab+3b^2=(a-b)^2+2b^2\ge2a^2/3>2a$. Direct substitution settles $a=1,2,3$ and gives equality at $(2,1)$.

## Arbitrarily large counterexamples

Take positive solutions of $p^2-2q^2=-1$ starting at $(7,5)$ and send $(p,q)$ to $(3p+4q,2p+3q)$. Set $(a,b)=(q,p-q)$. Since $D/q=4q-2p-1/q$, the ratio is

$$
\frac{p}{4q-2p-1}>\frac{1+\sqrt2}{2}.
$$

The strict inequality reduces to $2\sqrt2\,p>4q-1$. Squaring and using the Pell equation gives $8q>9$. The diameters are at least $q$, which grows without bound.

## Verification and attribution

`Statement.lean` defines Lebesgue area, the covering radius, and the lattice diameter using arbitrary collinear sets of lattice points. `Lines.lean` proves the equivalence with consecutive lattice strings in a convex region. The final theorems include `five`, `resolution`, `sharp_bound`, and `unbounded`.

```sh
# Run at the merge commit for PR #48.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

OpenAI Codex developed the square formulas and Pell construction and formalized the proofs. An independent agent audited the geometric definitions, the covering argument and the use of lattice-point counts. Searches for the authors, the proposed constant, square counterexamples and Pell constructions found no previous statement of the sharp square bound or of this unbounded family.
