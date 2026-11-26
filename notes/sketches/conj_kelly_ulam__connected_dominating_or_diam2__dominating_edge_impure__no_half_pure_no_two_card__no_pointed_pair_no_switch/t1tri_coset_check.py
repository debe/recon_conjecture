"""Numeric check of the symmetry of (OI) (sketch t1, section 4.4): for subgroups X, Y, Z,
XY cap XZ = X(Y cap Z) holds for one choice of the distinguished subgroup iff it holds for all
three.  Random subgroups of S_4 and S_5.  Evidence only; the sketch gives a paper argument."""
import random
from itertools import permutations


def compose(p, q):
    return tuple(p[i] for i in q)


def closure(gens, n):
    e = tuple(range(n))
    S, fr = {e}, [e]
    while fr:
        x = fr.pop()
        for g in gens:
            y = compose(g, x)
            if y not in S:
                S.add(y)
                fr.append(y)
    return frozenset(S)


def prod(X, Y):
    return {compose(x, y) for x in X for y in Y}


if __name__ == "__main__":
    rnd = random.Random(1)
    bad = fails = tot = 0
    for n in (4, 5):
        P = list(permutations(range(n)))
        for _ in range(400):
            X, Y, Z = [closure([rnd.choice(P) for _ in range(rnd.choice([1, 1, 2]))], n) for _ in range(3)]
            c = [prod(A, B) & prod(A, C) == prod(A, B & C) for A, B, C in ((X, Y, Z), (Y, X, Z), (Z, X, Y))]
            tot += 1
            fails += (not c[0])
            bad += len(set(c)) > 1
    print("triples of subgroups", tot, "| condition fails", fails, "| role-asymmetric", bad)
