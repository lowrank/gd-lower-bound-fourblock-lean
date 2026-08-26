"""Exact-rational experiments for the remaining side certificates."""

from collections import deque
from fractions import Fraction as Q
from functools import cache

from generate_fourblock_compact_certificate import qscaled_log_lower, qlog_exact


THLO = Q("0.4086960373221888")
THHI = Q("0.4086960373221890")
BLO = Q("0.8565576222695285")
BHI = Q("0.8565576222695288")
C2, C3 = Q("0.04"), Q("0.04")
D2, D3 = Q("0.0188"), Q("0.0583")
L2, L3 = Q("0.011"), Q("0.0468")
ALPHA = L3 - L2
K2LO, K2HI = D2 + BLO * L2, D2 + BHI * L2
K3LO = D3 + BLO * L3


def scale(y: Q) -> int:
    return 4 if y < Q(1, 8) else 3 if y < Q(1, 4) else 2 if y < Q(1, 2) else 1



def qscaled_log_upper(y: Q) -> Q:
    k = scale(y)
    return qlog_exact(y * 2**k)[1] - k * qlog_exact(Q(2))[0]


def q2_lower(zl: Q, zh: Q) -> Q:
    dzlo, dzhi = max(Q(0), zl - THHI), max(Q(0), zh - THLO)
    return (K2LO * BLO * dzlo - K2HI**2 * dzhi**2 / (4 * C2)
            - L2 * qscaled_log_upper(zh))


def run_q2():
    target = Q("0.009767")
    pending = deque([(THLO, Q("2.90"), 0)])
    leaves = checked = 0
    maxdepth = 0
    while pending:
        zl, zh, d = pending.popleft(); checked += 1
        if q2_lower(zl, zh) > target:
            leaves += 1; maxdepth = max(maxdepth, d); continue
        if d >= 60:
            raise RuntimeError((zl, zh, q2_lower(zl, zh)))
        zm = (zl + zh) / 2
        pending.extend([(zl, zm, d+1), (zm, zh, d+1)])
    print("Q2", checked, leaves, "depth", maxdepth)


def sqdist(vl: Q, vh: Q) -> Q:
    if vh < BLO: return (BLO - vh)**2
    if BHI < vl: return (vl - BHI)**2
    return Q(0)


def g_lower(zl: Q, zh: Q, vl: Q, vh: Q) -> Q:
    return (C3 * sqdist(vl, vh) + K3LO * vl * max(Q(0), zl - THHI)
            - ALPHA * qscaled_log_upper(zh))


def logq_lower(zl: Q, zh: Q, vh: Q) -> Q:
    return qscaled_log_lower(zl) - BHI * vh * max(Q(0), zh - THLO)


def run_g(qmax: Q, target: Q):
    zhi, vhi = Q("1.21"), 1 / THLO
    pending = deque([(THLO, zhi, Q(0), vhi, 0)])
    checked = leaves = infeasible = constrained = energy = 0
    maxdepth = 0
    logqmax = qscaled_log_upper(qmax)
    while pending:
        zl, zh, vl, vh, d = pending.popleft(); checked += 1
        if vl > 1 / zl:
            leaves += 1; infeasible += 1; continue
        if logq_lower(zl, zh, vh) > logqmax:
            leaves += 1; constrained += 1; continue
        if g_lower(zl, zh, vl, vh) > target:
            leaves += 1; energy += 1; maxdepth=max(maxdepth,d); continue
        if d >= 35:
            raise RuntimeError((qmax, target, zl, zh, vl, vh, g_lower(zl,zh,vl,vh)))
        # Binary split along the larger normalized coordinate uncertainty.
        if (zh-zl)/(Q("1.21")-THLO) >= (vh-vl)/vhi:
            mid=(zl+zh)/2
            pending.extend([(zl,mid,vl,vh,d+1),(mid,zh,vl,vh,d+1)])
        else:
            mid=(vl+vh)/2
            pending.extend([(zl,zh,vl,mid,d+1),(zl,zh,mid,vh,d+1)])
    print("G", qmax, target, "checked",checked,"leaves",leaves,
          "infeasible",infeasible,"constraint",constrained,"energy",energy,"depth",maxdepth)


if __name__ == "__main__":
    run_q2()
    run_g(Q("0.66"), Q("0.031960"))
    run_g(Q("0.82"), Q("0.030200"))
