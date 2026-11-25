# The seat increases that permit the Alabama paradox are determined by divisibility

With three states and $H$ seats, increasing the house by $k\ge1$ gives a positive probability of a state losing a seat exactly when

$$
k<H \quad\text{and}\quad H-k\nmid H.
$$

In particular, the largest possible jump is $H$ minus the least positive integer that does not divide $H$, for every $H\ge3$. David McCune found the maximum for odd houses and asked for the even case. The same criterion disproves his Conjecture 1 about monotonicity. The population vector in his model is uniform on the three-state simplex. [Original source, Proposition 1 and Conjecture 1](https://arxiv.org/html/2610.40682v1#S7)

For $H=9$, increasing to 15 seats gives a loss with probability zero, because $9-6=3$ divides 9. Increasing to 16 can cause a loss. Population shares $(12,12,1)/25$ give the allocation $(4,4,1)$ at 9 seats and $(8,8,0)$ at 16. Both allocations persist under small changes in the shares. Even houses can also have an increase late in the sequence. At $H=16$, jumps of 12 and 13 give zero and positive probability, respectively.

## The integer trapped between $k$ and $H$

Put $M=H+k$. Let $a_i,b_i$ be state $i$'s allocations before and after the increase. Hamilton's rule assigns the lower quotas and then fills the remaining seats in order of fractional remainder. Away from ties, the three rounding errors $Hp_i-a_i$ lie in an interval of width less than one. The same holds for $Mp_i-b_i$.

Consider the integers $D_i=Hb_i-Ma_i$. They sum to zero. Their range is less than $H+M$, since $D_i=M(Hp_i-a_i)-H(Mp_i-b_i)$. A state that loses a seat has $D_i\le-H-k$. Each of the other two integers is then less than $H$. Since their sum is at least $H+k$, each is greater than $k$.

This forces $k<H$. If $r=H-k$ divides $H$, it also divides $M=2H-r$ and every $D_i$. There is no multiple of $r$ strictly between $H-r$ and $H$. The boundary cases have probability zero because a tie lies on one of finitely many lines at each house size.

## Constructing a loss whenever the divisor test permits one

Suppose $r=H-k>0$ does not divide $H$ and put $j=\lfloor H/r\rfloor$. Try the allocations

$$
a=(H-j-1,j,1),\qquad b=(M-2j,2j,0).
$$

For the second state, $D_2=rj=H-(H\bmod r)$ lies strictly between $k$ and $H$. The first state's integer is $M-D_2$, in the same interval. For each of these two states choose $s_i$ with

$$
\frac{b_i-1}{M}<s_i<\frac{a_i}{H}.
$$

The inequalities on $D_i$ make these intervals nonempty. They also give $a_i-1<Hs_i<a_i$ and $b_i-1<Ms_i<b_i$. Set $p_3=(1-s_1-s_2)/3$ and $p_i=p_3+s_i$ for $i=1,2$. All shares are positive and sum to one. The rounding error for state 3 is the lowest at $H$ and highest at $M$. In each allocation its distance from each other error is less than one. These are strict Hamilton allocations throughout an open set of shares, so the loss has positive probability.

## Source and verification

McCune proposed the monotonicity conjecture and proved the sharp odd-house upper bound. Searches for the even-house maximum, loss probabilities for larger jumps, and a divisibility criterion found no earlier general solution. OpenAI Codex derived the criterion and formalized the proof.

The Lean statement uses the area of the loss event under the actual largest-remainder rule. The proof handles ties, proves the full divisibility criterion, and derives the maximum jump and the counterexamples. From the repository root, run

```sh
lake exe cache get
lake build conjectures.McCuneSeatJumps.Solution
lake env leanchecker conjectures.McCuneSeatJumps.Solution
```
