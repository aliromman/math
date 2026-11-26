# The gap in a tree domination conjecture can be arbitrarily large

For every positive integer $t$, there is a tree that $t$ mobile guards can defend at range three, even though it requires $2t$ stationary guards at range one. The tree also needs $t$ stationary guards at range three. This disproves Conjecture 8.2 of Clow and van Bommel with every positive integer as the gap.

The four-vertex path is already a counterexample. One mobile guard can cross the whole path in one move. A stationary guard at range one cannot cover both ends.

$$
\gamma_3(P_4)=\gamma^{\infty}_{\mathrm{all},3}(P_4)=1,
\qquad \gamma_1(P_4)=2.
$$

## The conjecture

The distance-$k$ domination number $\gamma_k(T)$ is the fewest stationary guards needed to place every vertex of $T$ within $k$ edges of a guard. For eternal domination, vertices come under attack one at a time. All guards may move up to $k$ edges after each attack. A guard must reach the attacked vertex. The least number that can answer every attack sequence is $\gamma^{\infty}_{\mathrm{all},k}(T)$. The paper permits guards to share a vertex.

Clow and van Bommel proved a result for trees at range two. They conjectured that for every finite tree and every integer $k>2$,

$$
\gamma_k(T)=\gamma^{\infty}_{\mathrm{all},k}(T)
\quad\Longrightarrow\quad
\gamma^{\infty}_{\mathrm{all},k}(T)=\gamma_{\lfloor k/2\rfloor}(T).
$$

See §8, Conjecture 8.2, in [*Eternal distance-2 domination in trees*, Ars Combinatoria 163 (2025), 29–49](https://doi.org/10.61091/ars163-03).

## Every odd range fails

Set $k=2h+1$ with $h\ge1$. A guard can cross the entire path $P_{2h+2}$ in one move because its length is $2h+1$. No vertex is within $h$ edges of both ends. Guards stationed at the two ends cover the path at range $h$. The three parameters are therefore $1,1,2$ at every odd range in the conjecture.

## An unbounded gap at range three

Start with any tree $B$ on $t$ vertices. At each vertex $A$ attach four new vertices with edges $AU$, $UB'$, $UV$, and $VC$. The old edges join the attachment vertices $A$.

```text
    B′
    |
A───U───V───C
```

Each block has diameter three. One mobile guard per block answers each attack by moving within its block. Every vertex outside a block is at least four edges from its leaf $C$, so each block also needs its own guard for stationary coverage at range three.

At range one the two leaves $B'$ and $C$ in a block have disjoint closed neighborhoods. These neighborhoods also stay inside their respective blocks. Thus the $2t$ leaves need $2t$ guards. Placing guards at every $U$ and $V$ meets the bound. The resulting tree $T$ satisfies

$$
\gamma_3(T)=\gamma^{\infty}_{\mathrm{all},3}(T)=t,
\qquad \gamma_1(T)=2t.
$$

## Prior work and attribution

Cox, Meger, and Messinger gave the eternal domination number of paths in Theorem 2 and recorded the stationary path formula. These earlier formulas already give the path values above. Searches for the conjecture number, the authors, odd ranges, and counterexamples found no earlier explicit disproof or arbitrary-tree construction giving this gap. OpenAI Codex identified the obstruction, constructed the family, and wrote the proofs. [Cox–Meger–Messinger, *Eternal distance-k domination on graphs* (2023)](https://doi.org/10.1007/s44007-023-00044-3)

## Verification

Run these commands from the repository root with the pinned Lean toolchain and Mathlib revision.

```sh
lake exe cache get
lake build conjectures.EternalTreeDomination.Solution
lake env leanchecker conjectures.EternalTreeDomination.Solution
```

`Statement.lean` gives the conjecture. `Solution.lean` proves the path formulas and the disproof. `Tree.lean` and `Blocks.lean` prove the arbitrary-tree construction and its three exact guard counts.
