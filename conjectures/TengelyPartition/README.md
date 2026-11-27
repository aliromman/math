# Proof of Tengely and Ulas’s Conjecture 4.6 on equal values of restricted partition functions

Write $P_a(n)$ for the number of ways to make $n$ using parts $1,2,a$. For **every** $3\le a<b$, the equation $P_a(x)=P_b(y)$ has solutions with both $x$ and $y$ arbitrarily large. This proves Conjecture 4.6 of Tengely and Ulas. Their Theorem 4.5 established a subfamily in which both third parts are multiples of four. [*Equal values of certain partition functions via Diophantine equations*, Research in Number Theory 7 (2021), §4](https://link.springer.com/article/10.1007/s40993-021-00293-7)

## A quadratic on each progression

Fix $0\le r<a$ and $t\ge1$. Count partitions of $a(2t-1)+r$ by the number of copies of $a$. The remaining amount can be made from ones and twos in $1+\lfloor n/2\rfloor$ ways. Reversing the order and pairing consecutive terms gives

$$
P_a\bigl(a(2t-1)+r\bigr)
=\sum_{j=0}^{2t-1}\left(1+\left\lfloor\frac{aj+r}{2}\right\rfloor\right)
=at^2+ct,
\qquad c=\left\lfloor\frac r2\right\rfloor+
\left\lfloor\frac{a+r}{2}\right\rfloor+2-a.
$$

The zero constant term lets us produce common values in two ways.

**If $ab$ is nonsquare**, take $r=a-1$, so $c=\lceil a/2\rceil$. Use $s=b-1$ and $d=\lceil b/2\rceil$ for the second partition function. For every positive Pell solution $X^2-abY^2=1$, put

$$
t=bcY^2+dXY,\qquad u=adY^2+cXY.
$$

Then $at^2+ct=bu^2+du$. The difference factors as $(bc^2-ad^2)Y^2(abY^2-X^2+1)$. Pell solutions have unbounded $Y$, so both partition arguments grow without bound.

**If $ab$ is square**, write $a=gA^2$ and $b=gB^2$. When $g\equiv2\pmod4$ choose $c=A$, $d=B$. Otherwise choose $c=d=0$. Both choices occur in the displayed formula. For odd $a=2h+1$, the attainable coefficients run from $1-h$ to $h+1$. For even $a=2h$, they run from $2-h$ to $h$ in steps of two. Thus $t=Bj$, $u=Aj$ give equal values for every positive $j$.

For example, the square-product pair $a=6,b=24$ permits $c=1,d=2$. Take $t=2j$ and $u=j$. The identity becomes

$$
P_6(24j-4)=P_{24}(48j-12)=24j^2+2j\qquad(j\ge1).
$$

## Verification and attribution

```sh
# Run at the merge commit for PR #97.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The statement counts the possible part multiplicities directly. Lean proves the quadratic formula by finite summation, constructs unbounded Pell solutions from Mathlib’s existence theorem, and covers square products by an explicit residue choice. Searches by conjecture number, authors, part sets and later work on equal values of restricted partition functions found the authors’ partial result and no earlier proof for all pairs. OpenAI Codex developed the constructions and the Lean proof.
