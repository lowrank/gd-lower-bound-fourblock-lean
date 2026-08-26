"""Generate an untrusted exact-rational branch-and-bound certificate for side G."""

import argparse
from collections import deque
from fractions import Fraction as Q
import json

from generate_fourblock_compact_certificate import qscaled_log_lower, qlog_exact


THLO = Q("0.4086960373221888")
THHI = Q("0.4086960373221890")
BLO = Q("0.8565576222695285")
BHI = Q("0.8565576222695288")
C3 = Q("0.04")
D3 = Q("0.0583")
L2 = Q("0.011")
L3 = Q("0.0468")
ALPHA = L3 - L2
K3LO = D3 + BLO * L3
ZHI = Q("1.21")
VHI = 1 / THLO


def pair(x: Q):
    return [x.numerator, x.denominator]


def scale(y: Q) -> int:
    return 4 if y < Q(1, 8) else 3 if y < Q(1, 4) else 2 if y < Q(1, 2) else 1


def qscaled_log_upper(y: Q) -> Q:
    k = scale(y)
    return qlog_exact(y * 2**k)[1] - k * qlog_exact(Q(2))[0]


def square_distance(vl: Q, vh: Q) -> Q:
    if vh < BLO:
        return (BLO - vh) ** 2
    if BHI < vl:
        return (vl - BHI) ** 2
    return Q(0)


def g_lower(zl: Q, zh: Q, vl: Q, vh: Q) -> Q:
    return (C3 * square_distance(vl, vh)
            + K3LO * vl * max(Q(0), zl - THHI)
            - ALPHA * qscaled_log_upper(zh))


def constraint_lower(zl: Q, zh: Q, vh: Q) -> Q:
    return qscaled_log_lower(zl) - BHI * vh * max(Q(0), zh - THLO)


def generate(qmax: Q, target: Q, max_depth: int):
    log_qmax_upper = qscaled_log_upper(qmax)
    pending = deque([(THLO, ZHI, Q(0), VHI, 0, "")])
    leaves = []
    checked = max_seen = 0
    counts = {"infeasible": 0, "constraint": 0, "energy": 0}
    while pending:
        zl, zh, vl, vh, depth, path = pending.popleft()
        checked += 1
        if vl > 1 / zl:
            kind = "infeasible"
        elif constraint_lower(zl, zh, vh) > log_qmax_upper:
            kind = "constraint"
        elif g_lower(zl, zh, vl, vh) > target:
            kind = "energy"
        else:
            if depth >= max_depth:
                raise RuntimeError({"depth": depth, "box": list(map(str, (zl, zh, vl, vh))),
                                    "lower": str(g_lower(zl, zh, vl, vh))})
            if (zh - zl) / (ZHI - THLO) >= (vh - vl) / VHI:
                mid = (zl + zh) / 2
                pending.append((zl, mid, vl, vh, depth + 1, path + "0"))
                pending.append((mid, zh, vl, vh, depth + 1, path + "1"))
            else:
                mid = (vl + vh) / 2
                pending.append((zl, zh, vl, mid, depth + 1, path + "0"))
                pending.append((zl, zh, mid, vh, depth + 1, path + "1"))
            continue
        counts[kind] += 1
        max_seen = max(max_seen, depth)
        leaves.append({"path": path, "kind": kind,
                       "box": [pair(x) for x in (zl, zh, vl, vh)]})
    return {"qmax": pair(qmax), "target": pair(target),
            "root": [pair(x) for x in (THLO, ZHI, Q(0), VHI)],
            "checked": checked, "max_depth": max_seen, "counts": counts,
            "leaves": leaves}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("qmax", type=Q)
    parser.add_argument("target", type=Q)
    parser.add_argument("output")
    parser.add_argument("--max-depth", type=int, default=35)
    args = parser.parse_args()
    data = generate(args.qmax, args.target, args.max_depth)
    with open(args.output, "w", encoding="utf-8") as stream:
        json.dump(data, stream, separators=(",", ":"))
    print(data["checked"], len(data["leaves"]), data["counts"], data["max_depth"])
