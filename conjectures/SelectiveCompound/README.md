# Solution to Beideman, Bowen and Müyesser’s Question 3 for finite-depth impartial games

Let $A$ be any impartial game position whose longest play takes $d$ moves. Add a Nim heap of size $k$. On each turn a player can move in the game, reduce the heap, or do both. The Grundy value of the combined position is exactly

$$
k+d \qquad\text{for every }k\ge\left\lfloor\frac{d^2}{4}\right\rfloor.
$$

The cutoff is best possible at every depth. At depth ten, for example, a game in the family below has value 28 with a heap of size 24. Increasing the heap to 25 raises the value to 35. Every subsequent stone adds one.

Beideman, Bowen and Müyesser asked which positions eventually reach the upper bound when the auxiliary heap grows. The answer is **every position of finite depth**. Theorem 2 of their paper gives a quadratic sufficient bound when the other game is a disjoint sum of Nim heaps. Their Theorem 6 fixes the auxiliary heap and varies the subtraction-game position. Such periodicity is consistent with saturation for each fixed position. [*The Sprague-Grundy Function for Some Selective Compound Games*, Integers 20 (2020), §3.1, Question 3](https://math.colgate.edu/~integers/ug4/ug4.pdf#page=18)

## Why the threshold works

Write $F_A(k)$ for the value. It is the least nonnegative integer missing from the values of the legal moves. Play lasts at most $k+d$ moves, so $F_A(k)\le k+d$. Increasing the heap preserves every old option and adds a move to the previous position. Thus $F_A$ is strictly increasing and its offset $F_A(k)-k$ never decreases.

Consider an entry below the upper bound. Write $r=F_A(k)-k$. We prove by induction on depth that some integer $m$ satisfies

$$
1\le m\le r+1,\qquad m\le d,\qquad k+1\le m(d-m).
$$

Choose an option $B$ of depth $d-1$. Its increasing sequence omits at most $d-1$ integers, since $F_B(j)\le j+d-1$. If none of the first $k+1$ values of $A$ occurs in this sequence, take $m=1$.

Otherwise let $i\le k$ be the last shared entry and write $F_A(i)=F_B(j)$. Necessarily $i<j$. If $j\le i$, moving from $A$ to $B$ with heap $j$ would reproduce the current Grundy value. Put $s=F_B(j)-j$. The offset at $A$ is already at least $s+1$ at entry $i$, so $s<d-1$. The child has used $s$ of its omissions below the shared value. The next $k-i$ entries of $A$ therefore fit among at most $d-1-s$ remaining omissions.

Apply the induction hypothesis at the child's entry $j$. It gives $j+1\le m(d-1-m)$ with $m\le s+1$. Since $i<j$,

$$
k+1\le (j+1)+(d-2-s)
      \le m(d-1-m)+(d-1-m)
      =(m+1)(d-1-m).
$$

This proves the induction step. The product of two nonnegative integers with sum $d$ is at most $\lfloor d^2/4\rfloor$. An entry below the upper bound must therefore have $k<\lfloor d^2/4\rfloor$.

## Games that attain the cutoff

Start with an ordinary heap of size $q$. Place $p$ new positions in a chain above it. From its $`i`$th position, a player can move to the preceding position or to any ordinary heap of size less than $i-1$. The top position has depth $p+q$. For $p\ge1$ its value with the auxiliary heap is

$$
F(k)=
\begin{cases}
k+p-1 & k\lt pq,\\
k+p+q & k\ge pq.
\end{cases}
$$

The small heaps force the first offset to be at least $p-1$. Below $pq$ the two ranges of the preceding position both miss $k+p-1$. From $pq$ onward that position supplies every value from $k+p-1$ through $k+p+q-1$ by retaining between $k-q$ and $k$ auxiliary stones. Induction along the chain gives the formula. Choosing $p=\lfloor d/2\rfloor$ and $q=\lceil d/2\rceil$ gives the sharp cutoff.

## Verification and attribution

Run these commands from the repository root with its pinned Lean and Mathlib releases.

```sh
# Run at the merge commit for PR #50.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines the game, the legal selective moves, the Grundy value, and the property in Question 3. Positions can have arbitrary branching. The depth conditions say that every option is shorter and that some option begins a longest play. `Grundy.lean` proves the least-excluded-value properties. `Extremal.lean` constructs the games above, and `Solution.lean` proves the bound.

OpenAI Codex derived the general threshold and its sharp examples, wrote the Lean proofs, and checked them against the source. Searches covering the original paper, subsequent papers on selective compounds, and work on Sprague–Grundy-decreasing games found no earlier universal sharp threshold.
