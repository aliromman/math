# Disproof of Mascia, Rinaldo and Romeo’s Conjecture 1.2 on zig-zag walks and prime polyomino ideals

The polyomino below has no zig-zag walk. Over every field, the quotient by its polyomino ideal contains two nonzero elements whose product is zero. Under the printed common-rectangle condition (Z3), this disproves the implication from absence of a walk to primality in Conjectures 1.2 and 4.6 of Mascia, Rinaldo and Romeo. It also contradicts the finite assertion through 14 cells in Theorems 1.1 and 3.9. [Original paper, Illinois Journal of Mathematics 64 (2020), 291–304](https://doi.org/10.1215/00192082-8591560) · [Author manuscript](https://arxiv.org/abs/1907.08438)

```text
    x = 0 1 2 3
y = 4   · ■ ■ ·
    3   ■ · ■ ■
    2   ■ ■ ■ ·
    1   ■ · ■ ■
    0   · ■ ■ ·
```

Each square is named by its lower left corner. Attach a variable $x_{ij}$ to every lattice vertex $(i,j)$ of the shape. Whenever a rectangle consists entirely of occupied squares, equate the products of the variables on its two diagonals. These relations generate the polyomino ideal $I$. Primality would permit cancellation of every nonzero element in the quotient ring.

## Two nonzero factors have zero product

In the table, $ij$ means $(i,j)$. In each row, $v_i,z_i$ are opposite corners of an occupied rectangle, as are $v_{i+1},u_i$. Take $v_7=v_1$.

| $i$ | $v_i$ | $z_i$ | $u_i$ |
|---|---|---|---|
| 1 | 11 | 04 | 01 |
| 2 | 14 | 25 | 15 |
| 3 | 24 | 43 | 44 |
| 4 | 23 | 02 | 03 |
| 5 | 22 | 41 | 42 |
| 6 | 21 | 10 | 20 |

Write $Z=\prod_i x_{z_i}$ and $U=\prod_i x_{u_i}$. Starting with $x_{11}Z$, replace $x_{v_i}x_{z_i}$ by $x_{v_{i+1}}x_{u_i}$ in order. This gives $x_{11}U$ after six steps.

Thus $x_{11}(Z-U)=0$ in the quotient. Setting every variable to one respects all rectangle relations and gives $x_{11}=1$. For the other factor, set the six $z_i$ variables to one and all other variables to zero. No two $z_i$ are opposite corners of an occupied rectangle, as one can check in the diagram. Every rectangle relation becomes $0=0$, and $Z-U=1$. This proves nonprimality.

## Why there is no zig-zag walk

Definition 3.2 requires consecutive rectangles to meet in just one corner. Within each rectangle, the incoming and outgoing corners must share a side. The marked corner $z$ is opposite the incoming corner. Condition (Z3) forbids any two marked corners from lying in a common occupied rectangle, including on one edge. In the six rows above, $04$ and $02$ lie on the left edge of the same rectangle. Reversing the sequence also fails, because $01$ and $03$ share that edge.

Five occupied rectangles cover all 26 vertices. Their opposite corners are $(01,14)$, $(21,42)$, $(14,35)$, $(23,44)$ and $(10,31)$. Consequently a zig-zag walk has at most five marks. The following finite check excludes every length. Enumerate all occupied rectangles and their eight oriented sides. From a side $s$, continue at its endpoint into the opposite quadrant. Reject a new side when its mark and an earlier mark lie in a common occupied rectangle.

| Number of sides | Paths left after the mark test |
|---|---:|
| 1 | 264 |
| 2 | 304 |
| 3 | 288 |
| 4 | 156 |
| 5 | 40 |
| 6 | 0 |

No surviving path closes. These counts allow a rectangle to occur more than once, so the check also covers the paper’s requirement that all rectangles be distinct. The Lean proof computes the test and proves that every walk in the definition must pass it.

## The earlier finite check

The authors’ reference code tests (Z3) by asking whether an occupied rectangle contains the bounding box of each pair of marks. This includes collinear pairs. Its closed-walk search can also accept a sequence of odd length whose first rectangle has opposite incoming and outgoing corners. For example, the rectangles with opposite corners $(21,33)$, $(33,44)$, $(14,35)$, $(01,14)$ and $(10,21)$ pass that closure test. The first rectangle meets its neighbors at $21$ and $33$. Those points fail the shared-side condition (Z2). The mark extraction omits that rectangle and checks only the remaining four marks. [Authors’ implementation and description](https://www.giancarlorinaldo.it/polyominoes-primality.html)

A search of the original paper, the authors’ implementation, later work on special classes, and publications citing the conjecture found no earlier general disproof. The six rectangles above do satisfy the alternative rule that forbids only opposite-corner pairs among the marks. That rule changes (Z3). [2026 result on dilated closed paths](https://arxiv.org/abs/2609.30086)

Giancarlo Rinaldo and his coauthors are investigating the counterexample and the reported implementation issue. Their investigation is ongoing. Navarra and Qureshi also state the common-rectangle test in Definition 3.7 of their survey. [Survey, Theorem 3.10 and Conjecture 3.11](https://arxiv.org/pdf/2511.22778#page=8)

## Verification

From the repository root, run

```sh
# Run at the merge commit for PR #64.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines the conjecture for an arbitrary coefficient field. `Solution.lean` proves its negation for every field and checks the transitive axioms. AI agents found the counterexample, derived the zero divisors, wrote the Lean proof and independently audited the result.

Carla Mascia, Giancarlo Rinaldo and Francesco Romeo, Primality of multiply connected polyominoes, Conjecture 1.2 under the printed condition (Z3) of Definition 3.2. [Publication](https://arxiv.org/pdf/1907.08438#page=2)
