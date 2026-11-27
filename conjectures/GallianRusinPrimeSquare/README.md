# Proof of Gallian and Rusin’s conjecture on the number of solution dice with p²q sides

For any two distinct primes $p,q$, **exactly 22** labelings of a $p^2q$-sided die can appear in a game with the sum frequencies of ordinary dice. Every one occurs in a game of three dice. Thus 12-sided dice and 18-sided dice, for example, have the same count despite their different face counts.

Gallian and Rusin allow any finite number of dice greater than one. Labels are positive integers and can repeat. Labelings that differ only in the order of the faces count once. The authors exhibited 22 labelings and conjectured these were all. Chao, Gabel, Larson, and Nasr later classified the eight games with two dice. [Gallian and Rusin, pp. 245 and 259](https://www.cs.umd.edu/users/gasarch/BLOGPAPERS/nonstandarddice.pdf#page=15) · [Chao et al., Theorem 4.6](https://arxiv.org/html/2408.10331v1#S4.Thmtheorem4)

## Which dice work?

Write $A_r=1+x+\cdots+x^{r-1}$ and let $\Phi_j$ be the $j$th cyclotomic polynomial. Encode a die by $P(x)$, with the coefficient of $x^k$ equal to the number of faces labeled $k+1$. The 22 polynomials are

$$
P=A_q A_p^a A_p(x^p)^b\Phi_{pq}^c\Phi_{p^2q}^d,\qquad
a+b=2,\quad c\le a+1,\quad d\le b+\boldsymbol{1}_{c>0},
$$

where all exponents are nonnegative integers. The choices $a=0,1,2$ give 7, 8, and 7 polynomials. For example, $a=2$ and $b=c=d=0$ gives the labels $1+i+j+k$ with $0\le i,j<p$ and $0\le k<q$.

In an $n$-dice game the polynomials multiply to $A_{p^2q}^n$. Unique factorization gives just five possible factors. Evaluation at 1 gives the displayed powers of the three prime-power factors. The factors $\Phi_{pq}$ and $\Phi_{p^2q}$ both take the value 1 there. The coefficient of $x$ is $a+1-c$, which gives the first inequality.

## Why the last exponent is bounded

Put $D=\Phi_{p^2q}$. The identity $A_p(x^p)D=A_p(x^{pq})$ lets us remove one copy of $D$ from $P$ by multiplying by $A_p(x^p)$, as far as coefficients below degree $pq$ are concerned. This preserves their nonnegativity. It therefore suffices to rule out the *first* excess exponent.

When $c>0$, write $u=c-1$, $t=a-u$, and $B=A_p^t A_p(x^q)^u$. At $d=b+2$, the coefficients below $\min(p^2,pq)$ equal those of $(1-x^p)B$. To see this, use $A_q\Phi_{pq}=A_q(x^p)$, $A_q(x^p)D=A_q(x^{p^2})$, and $(1-x^{p^2})D=(1-x^p)A_p(x^{pq})$.

Since $t+u\le2$, there are only six forms of $B$. For $1,A_p,A_p(x^q),A_p(x^q)^2$, the difference is negative at degree $p$. For $A_p^2$, it is negative at $2p-1$. For the mixed product $A_p A_p(x^q)$ set $h=\lfloor p/q\rfloor$. The coefficients at $qh$ and $p+qh$ are $h+1$ and $h$. Their difference is $-1$, at degree $p+qh<2p$.

When $c=0$, set $s=p^2$, $U=A_p^{a+1}$, and $N=(a+1)(p-1)$. At $d=b+1$ there is an exact identity

$$
(1-x^s)P=(1-x^q)U A_p(x^{pq})^{b+1}.
$$

The support of $U$ is the entire interval $[0,N]$ and $N<s$. Extend its coefficients periodically by $v_i=[x^{i\bmod s}]U$. For $q\le i<pq$, the identity gives $[x^i]P=v_i-v_{i-q}$. Write $r=q\bmod s>0$. If $N+1<s$ and $N+1<pq$, choose $j=\max(0,N+1-r)$. Then $v_j>0$, $v_{q+j}=0$, and $q+j<pq$. This gives a negative coefficient.

These two inequalities hold except possibly when $a=2$ and one prime is 2. If $p=2$, the period is $(1,3,3,1)$. Choose $j=2$ for $q\equiv1\pmod4$, or $j=1$ for $q\equiv3\pmod4$. If $q=2$, the coefficient at $2p-1$ is $[x^{2p-1}](1-x^2)A_p^3=2-2p<0$.

Conversely, every allowed product splits into three geometric sums. Pair $\Phi_{pq}$ with $A_p$ or $A_q$, and pair $D$ with $A_p(x^p)$ or $A_q(x^p)$. These pairings give nonnegative coefficients and $p^2q$ faces. For each allowed exponent tuple, two more allowed tuples bring every exponent total to 3. The three polynomials therefore multiply to $A_{p^2q}^3$. Lean verifies these 22 finite choices and proves the products are distinct.

## Verification

From the repository root, run

```sh
# Run at the merge commit for PR #65.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` states the original conjecture using the shared [dice model](../GallianRusin/Die.lean). The axiom checks in `Solution.lean` cover the classification, the three-dice realization, and the exact count. Searches for the conjecture, polynomial dice, nonstandard number generators, and subsequent work on dice relabeling found the two-dice result above and no earlier proof for games of arbitrary size. AI developed the proof and Lean formalization. Gallian and Rusin introduced the cyclotomic representation and the lower bound of 22.
