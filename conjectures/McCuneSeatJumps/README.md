# Disproof of McCune’s Conjecture 1 on Alabama-paradox probabilities

When a legislature adds seats under Hamilton’s largest-remainder rule, a state can lose a seat. With three states and uniformly distributed population shares, the probability of a loss after an increase of $k$ seats from a house of size $H$ is

$$
p_k(H)=\frac{g^3}{3H^2(H+k)^2}\sum_{\ell=1}^H (t_\ell^3-t_\ell),
\qquad g=\gcd(H,k),\qquad
t_\ell=\frac{\max(0,H+2k-3k\ell)}{g}.
$$

The formula holds for all positive integers $H,k$. A loss has positive probability precisely when **$k<H$ and $H-k$ does not divide $H$**. For $H\ge3$, the largest such jump is $H$ minus its least positive nondivisor.

David McCune derived the one-seat probability, determined the maximum jump for odd houses and conjectured how the probabilities decrease for each parity. They can rise even between two positive terms. For an odd house, $p_9(27)=1/648<544/332667=p_{10}(27)$. For an even house, $p_{10}(30)=1/720<38/25215=p_{11}(30)$. [Original paper, Theorem 1, Proposition 1 and Conjecture 1](https://arxiv.org/html/2610.40682v1)

## Where the formula comes from

Let $M=H+k$. An allocation $a$ to a population vector $p$ is a strict Hamilton allocation if its entries sum to $H$ and the rounding errors $Hp_i-a_i$ differ pairwise by less than one. Their sum is zero. With three states, every error is strictly between $-2/3$ and $2/3$. The same applies to the new allocation $b$. Ties lie on lines and have area zero.

These bounds imply that a losing state drops just one seat and is the only loser. Suppose it falls from $\ell$ to $\ell-1$. For each of the other states, write $A,B$ for its old and new allocations. Its population share minus the loser’s share lies in the interval

$$
\frac{B-\ell}{M}<s<\frac{A-\ell+1}{H}.
$$

The two differences describe a rectangle. Its side lengths have denominator $HM$. Their integer numerators sum to $W=H+2k-3k\ell$. When both are positive, each is less than $H$. The two interval bounds then imply all rounding inequalities in both houses. The population shares are positive, so the whole rectangle represents an actual loss. Different old allocations or different losers give disjoint rectangles.

For fixed $\ell$ and $A$, the first width numerator is the residue of $k(A+1-\ell)$ modulo $H$. Only residues $0<r<W$ contribute, and the second width numerator is $W-r$. There is exactly one new allocation for each contributing residue and old allocation. Extending $A=0,\ldots,H-\ell$ to a full residue system adds only zero terms. Each multiple of $g$ occurs $g$ times. Thus the sum of the width products is $g^3\sum_{j=0}^{t_\ell}j(t_\ell-j)=g^3(t_\ell^3-t_\ell)/6$.

The change from two shares to two share differences has determinant three. The probability density on the unit population triangle is two, and there are three choices of loser. These factors give the displayed formula. Its first summand is positive exactly when $H-k\ge2g$. Since $g=\gcd(H,H-k)$ for $k<H$, this gives the divisibility criterion.

For example, a jump from 9 to 15 seats has zero probability of a loss. A jump from 9 to 16 can take a seat away. Shares $(12,12,1)/25$ give $(4,4,1)$ at 9 seats and $(8,8,0)$ at 16.

## Verification and attribution

The Lean statement uses the uniform area of the loss event under the largest-remainder rule, including ties. The proof establishes the formula, its support and maximum, the failure of the original conjecture, and the four positive probabilities above. From the repository root, run

```sh
# Run at the merge commit for PR #37.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

McCune supplied the model, the conjecture and the one-seat calculation. Searches for prior work on larger jumps found no earlier general formula. OpenAI Codex agents derived and formalized it. An independent agent checked the proof against the original model and compared it with exact polygon intersections for 71 pairs of house sizes and jumps.
