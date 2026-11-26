"""Write the orientation constraints for a fixed Erdős–Szekeres extension to DIMACS."""
from argparse import ArgumentParser
from itertools import combinations, product
from shutil import copyfileobj
from sys import stdout
from tempfile import TemporaryFile

# The point with label i has coordinates (i, HEIGHTS[i]).
HEIGHTS = (0, 5, 9, 12, 14, 15, 193, 196, 198, 199, 221, 223, 224, 229, 230,
           232, 3537, 3539, 3540, 3545, 3546, 3548, 3570, 3571, 3573, 3576,
           49798, 49799, 49801, 49804, 49808, 280909)
TRUE, FALSE = 1, -1


class Formula:
    def __init__(self, output):
        self.output = output
        self.variables = self.clauses = 1
        output.write("1 0\n")

    def variable(self):
        self.variables += 1
        return self.variables

    def add(self, *literals):
        if TRUE in literals:
            return
        terms = (str(v) for v in literals if v != FALSE)
        self.output.write(" ".join(terms) + " 0\n")
        self.clauses += 1

    def sign_product(self, *literals):
        polarity = -1 if sum(v < 0 for v in literals) % 2 else 1
        variables = [abs(v) for v in literals if abs(v) != TRUE]
        if not variables:
            return polarity * TRUE
        if len(variables) == 1:
            return polarity * variables[0]
        output = self.variable()
        for signs in product((-1, 1), repeat=len(variables)):
            result = -1 if signs.count(-1) % 2 else 1
            self.add(*(-s * v for s, v in zip(signs, variables)), result * output)
        return polarity * output


def area(i, j, k):
    return (j - i) * (HEIGHTS[k] - HEIGHTS[i]) - (k - i) * (HEIGHTS[j] - HEIGHTS[i])


def deletion_pairs():
    seen = set()
    for pair in combinations(range(32), 2):
        kept = [i for i in range(32) if i not in pair]
        keys = []
        for order in (kept, kept[::-1]):
            signs = bytes(area(i, j, k) > 0 for i, j, k in combinations(order, 3))
            keys.append(bytes(v ^ signs[0] for v in signs))
        key = min(keys)
        if key not in seen:
            seen.add(key)
            yield pair


def orientations(f, anchors, points):
    turn = {}
    for a, b, c in combinations(points, 3):
        if c < len(anchors):
            i, j, k = (anchors[p] for p in (a, b, c))
            determinant = area(i, j, k)
            assert determinant
            sign = TRUE if determinant > 0 else FALSE
        else:
            sign = f.variable()
        turn[a, b, c] = turn[b, c, a] = turn[c, a, b] = sign
        turn[c, b, a] = turn[b, a, c] = turn[a, c, b] = -sign
    return turn


def radial_orders(f, turn, old, points):
    for p in points:
        ref = 1 if p == 0 else 0
        others = [i for i in points if i not in (p, ref)]
        before = {}
        for a, b in combinations(others, 2):
            before[a, b] = f.sign_product(turn[p, ref, a], turn[p, ref, b], turn[p, a, b])
            if p == 0 and a >= old:
                f.add(before[a, b])
        for a, b, c in combinations(others, 3):
            ab, bc, ac = before[a, b], before[b, c], before[a, c]
            f.add(-ab, -bc, ac)
            f.add(ab, bc, -ac)


def hexagon_extensions(f, turn, old, points):
    def chain(vertices):
        row = []
        for v in vertices:
            while len(row) >= 2 and turn[row[-2], row[-1], v] == FALSE:
                row.pop()
            row.append(v)
        return row[:-1]

    wedges = set()
    for six in combinations(range(old), 6):
        hull = chain(six) + chain(reversed(six))
        if len(hull) == 6:
            cycle = hull + hull[:3]
            for i in range(6):
                wedges.add(tuple(cycle[i:i + 4]))
    for a, b, c, d in sorted(wedges):
        for q in range(old, len(points)):
            f.add(-turn[a, b, q], turn[b, c, q], -turn[c, d, q])


def forbidden_polygons(f, turn, old, points):
    convex = {}
    for a, b, c, d in combinations(points, 4):
        coeff = (turn[b, c, d], -turn[a, c, d], turn[a, b, d], -turn[a, b, c])
        if d < old:
            convex[a, b, c, d] = TRUE if coeff.count(TRUE) == 2 else FALSE
            continue
        f.add(*coeff)
        f.add(*(-v for v in coeff))
        flag = convex[a, b, c, d] = f.variable()
        for plus in combinations(range(4), 2):
            f.add(*(v if i not in plus else -v for i, v in enumerate(coeff)), flag)
    free = range(old, len(points))
    for k in range(min(7, len(free)) + 1):
        for fixed in combinations(range(old), 7 - k):
            if any(convex[q] == FALSE for q in combinations(fixed, 4)):
                continue
            for new in combinations(free, k):
                f.add(*(-convex[q] for q in combinations(fixed + new, 4)))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=("32", "33", "pairs"))
    parser.add_argument("--omit", nargs="+", type=int, default=[0, 2, 12, 17, 28])
    args = parser.parse_args()
    if args.case == "pairs":
        for pair in deletion_pairs():
            print(*pair)
        return
    if any(i not in range(32) for i in args.omit) or len(set(args.omit)) > 30:
        parser.error("use labels from 0 to 31 and retain at least two points")
    anchors = [i for i in range(32) if i not in args.omit]
    points = range(int(args.case))
    with TemporaryFile(mode="w+t") as body:
        f = Formula(body)
        turn = orientations(f, anchors, points)
        radial_orders(f, turn, len(anchors), points)
        hexagon_extensions(f, turn, len(anchors), points)
        forbidden_polygons(f, turn, len(anchors), points)
        print(f"p cnf {f.variables} {f.clauses}")
        body.seek(0)
        copyfileobj(body, stdout)


if __name__ == "__main__":
    main()
