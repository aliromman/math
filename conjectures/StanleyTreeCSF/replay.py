"""Check the three-site construction in README.md with exact integers."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations


def node(children):
    return tuple(sorted(children))


@cache
def rooted_trees(order):
    if order == 1:
        return ((),)
    branches = [(k, t) for k in range(1, order) for t in rooted_trees(k)]

    def fill(left, start, children):
        if left == 0:
            yield node(children)
            return
        for i in range(start, len(branches)):
            k, branch = branches[i]
            if k > left:
                break
            yield from fill(left - k, i, children + (branch,))

    return tuple(sorted(fill(order - 1, 0, ())))


def switched_trees(lobes):
    arms = [node(t for i, t in enumerate(lobes) if i != j) for j in range(3)]
    for p in permutations(range(3)):
        yield node(node(lobes[i] + lobes[j] + (arms[j],)) for i, j in enumerate(p))


@cache
def evaluations(tree):
    # Root states for the Ising polynomial and the proper-coloring function.
    plus, minus = 3, 1
    rgb = [2, 3, 5]
    for branch in tree:
        a, b, colors = evaluations(branch)
        plus *= a + 2 * b
        minus *= 2 * a + b
        total = sum(colors)
        for i in range(3):
            rgb[i] *= total - colors[i]
    return plus, minus, tuple(rgb)


def cut_spectrum(tree, k):
    # Preorder makes each rooted subtree one interval of vertex indices.
    end = []

    def visit(t):
        i = len(end)
        end.append(0)
        for child in t:
            visit(child)
        end[i] = len(end)

    visit(tree)
    counts = Counter()
    for cuts in combinations(range(1, len(end)), k):
        roots = (0,) + cuts
        sizes = [end[v] - v for v in roots]
        for i, v in enumerate(cuts, start=1):
            j = i - 1
            while end[roots[j]] <= v:
                j -= 1
            sizes[j] -= end[v] - v
        counts[tuple(sorted(sizes))] += 1
    return counts


def main():
    for k in range(4, 8):
        ising, chromatic = set(), set()
        count = 0
        for lobes in combinations(rooted_trees(k), 3):
            for tree in switched_trees(lobes):
                plus, minus, colors = evaluations(tree)
                ising.add(plus + minus)
                chromatic.add(sum(colors))
                count += 1
            evaluations.cache_clear()
        print(12 * k + 1, count, len(ising), len(chromatic))
        assert count == len(ising) == len(chromatic)

    rotations = list(switched_trees(rooted_trees(4)[:3]))
    left, right = rotations[3:5]
    for k in range(4):
        assert cut_spectrum(left, k) == cut_spectrum(right, k)
    partition = (1, 1, 3, 11, 33)
    counts = tuple(cut_spectrum(t, 4)[partition] for t in (left, right))
    print(partition, counts)
    assert counts == (208, 207)


if __name__ == "__main__":
    main()
