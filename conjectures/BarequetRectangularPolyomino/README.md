# Minimum totally concave polyominoes can have rectangular bounding boxes

For every integer $t\ge4$, there is a minimum-area $t$-fold totally concave polyomino with bounding box $(3t+4)\times(3t+2)$. The smallest new example has 149 cells in a $16\times14$ box. Each row and each column of its box has five occupied runs.

```text
#####.##.#.###.#
.#.#.##.####.###
#.###.###..##..#
###.##.#.##.###.
.#.#.####.###.##
#.####..##..##.#
###.#.##.###.##.
.#.###.###.##.##
..#..##..##.##.#
#.###.###.##.##.
###.###.##.##.##
..##..##.##.##.#
##.###.##.##.##.
.###.##.##.##.##
```

A polyomino is a finite set of grid cells connected along their sides. It is $t$-fold totally concave if each row and column of its bounding box has at least $t$ gaps between occupied runs. Barequet, Madras and Peters proved that the minimum area is $6(t+1)^2-1$ for $t\ge3$. They constructed square minimizers at every such order and exhibited a $13\times11$ minimizer at $t=3$. Section 3.3 asks if nonsquare minimizers exist past that order. Their Theorem 7 gives the two possible shapes of the bounding box. The construction here realizes the second shape at every order. [Barequet, Madras and Peters, CCCG 2025, pp. 92–95](https://cccg-wads-2025.eecs.yorku.ca/cccg-papers/34.pdf)

## Construction

Put $u=t+1$. Draw $u+1$ columns and $u$ rows of $3\times3$ blocks. Keep only the leftmost column of cells in the last block column and the bottom two rows of cells in the top block row. Number blocks $(i,j)$ from the lower left, starting at zero. The table specifies each block by its binary mask. Bit $3s+r$ indicates whether the cell at local coordinates $(r,s)$ is occupied.

| Block | Mask |
| --- | --- |
| Right edge $i=u$ | 73 at the top, 65 elsewhere |
| Left edge $i=0$ | 286 at $j=0$, 303 at $j=1$, 378 elsewhere |
| Top edge $j=u-1$, excluding the two cases above | 286 at $i=j$, 495 at $i=j-1$, 221 elsewhere |
| Other blocks | 286 at $i=j$, 125 at $i=j+1$, 471 at $i=j-1$, 245 elsewhere |

Away from these edges and the main diagonal, the occupied cells form staircases. In a block of type 245 the empty cells satisfy $x+y\equiv1\pmod3$. The three diagonal blocks join the staircases. The edge blocks close the pattern at the sides.

## Area, gaps and connectivity

Count occupied cells one row of blocks at a time. The first two rows each contain $6u+1$ cells. The next $u-3$ rows each contain $6u+2$. The top two rows of individual cells contain $4u+3$ cells together. Their sum is $6u^2-1$, the known minimum. The Lean proof includes the lower bound for comparison with every admissible polyomino.

To count runs, mark each cell with its horizontal and vertical prefix counts. At block $(i,j)$ these counts have the form $i+R$ and $j+C$, with corrections that depend only on the local block type and position. Across one cell the count increases by one exactly when an occupied run begins. The count starts at zero and ends at $u$ on each line.

For connectivity, give each occupied cell the integer rank $12\max(i,j)+D$. At every occupied cell except $(1,0)$, one of the four occupied neighbors has smaller rank. Following smaller ranks reaches $(1,0)$ because the region is finite. The file `Tiles.lean` contains the corrections and the rank offsets. Distances beyond five blocks leave the local checks unchanged. To verify every box size, sort the block coordinates as $0\le\min(i,j)\le\max(i,j)\le u$ and truncate each of the three gaps to six. This preserves all relevant clipped distances, including those of adjacent cells. Lean checks both coordinate orders and all nine cell positions in each resulting case. `Geometry.lean` turns these local identities into counts and connectivity for the entire rectangle.

## Verification and attribution

From the repository root, run

```sh
lake build conjectures.BarequetRectangularPolyomino.Solution
lake env leanchecker conjectures.BarequetRectangularPolyomino.Solution
```

`Statement.lean` defines the original existence question. `Solution.lean` proves it and the stronger construction for every $t\ge4$. Its axiom guards check both theorems.

The minimum-area formula and the $t=3$ nonsquare example are due to Barequet, Madras and Peters. The five-author October 2025 preprint still lists the nonsquare case as open on page 12 and records on page 23 that no example was known for any $t>3$. Searches for the authors, the bounding-box question, and the proposed side lengths found no earlier construction for $t>3$. [Barequet, Keren, Madras, Peters and Rivkin, 2025](https://yorkspace.library.yorku.ca/bitstreams/7075605b-2c59-41b9-982e-fdd9c6065963/download)

OpenAI Codex used a finite constraint search to find the tiles, derived the uniform counting and connectivity certificates, and wrote the Lean proof.
