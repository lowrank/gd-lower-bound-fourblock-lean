"""Generate the compact rational central four-block certificate.

The script is deliberately untrusted.  Its output is accepted only after all
short rational witnesses and all tree leaves are recomputed by Lean.
"""

from collections import deque
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import isqrt
import argparse
import json


SCALE = 10 ** 12
LOG_STEPS = 8
GUARD = Decimal("1e-28")


def qfloor(x: Q, scale: int = SCALE) -> Q:
    return Q((x.numerator * scale) // x.denominator, scale)


def qceil(x: Q, scale: int = SCALE) -> Q:
    return -qfloor(-x, scale)


def qsqrt_bounds(x: Q, scale: int = SCALE) -> tuple[Q, Q]:
    n = isqrt((x.numerator * scale * scale) // x.denominator)
    lo = Q(n, scale)
    while (lo + Q(1, scale)) ** 2 <= x:
        lo += Q(1, scale)
    while lo * lo > x:
        lo -= Q(1, scale)
    return lo, lo if lo * lo == x else lo + Q(1, scale)


def qlog_bounds(y: Q, n: int = LOG_STEPS) -> tuple[Q, Q]:
    x = (y - 1) / (y + 1)
    series = sum((x ** (2 * i + 1) / (2 * i + 1) for i in range(n)), Q(0))
    error = abs(x) ** (2 * n + 1) / (1 - x * x)
    return qfloor(2 * (series - error)), qceil(2 * (series + error))


def qlog_exact(y: Q, n: int = LOG_STEPS) -> tuple[Q, Q]:
    x = (y - 1) / (y + 1)
    series = sum((x ** (2 * i + 1) / (2 * i + 1) for i in range(n)), Q(0))
    error = abs(x) ** (2 * n + 1) / (1 - x * x)
    return 2 * (series - error), 2 * (series + error)


def qscaled_log_lower(y: Q) -> Q:
    k = 4 if y < Q(1, 8) else 3 if y < Q(1, 4) else 2 if y < Q(1, 2) else 1
    return qlog_exact(y * 2 ** k)[0] - k * qlog_exact(Q(2))[1]


Q_TH_LO = Q("0.4086960373221888")
Q_TH_HI = Q("0.4086960373221890")
Q_B_LO = Q("0.8565576222695285")
Q_CBASE = Q(927669024051, 10**13)
Q_C4 = Q(9658, 100000)
Q_D4 = Q(49302, 100000)
Q_L2 = Q(11, 1000)
Q_ALPHA = Q(358, 10000)
Q_L3 = Q(468, 10000)


def qcentral_endpoint(z: Q) -> Q:
    raw = Q_D4 * Q_B_LO * (z - Q_TH_HI) - Q_D4**2 * (z - Q_TH_LO)**2 / (4 * Q_C4)
    return max(Q(0), raw)


def qcentral_energy(z: Q, r: Q, s: Q) -> Q:
    ep = qcentral_endpoint(z)
    value = (Q_CBASE + ep + Q_L2 * qscaled_log_lower(r) +
             Q_ALPHA * qscaled_log_lower(s) + Q_L3 * qscaled_log_lower(z))
    return max(ep, value)


def qedge(u: Q, v: Q) -> Q:
    return u * v / (2 * (u + v))


def kernel_jet(u: Q, v: Q) -> dict:
    b = qedge(u, v)
    x = 4 * b * b + 1
    sqrt_lo, sqrt_hi = qsqrt_bounds(x)
    dlo = qfloor(2 / (2 * b + 1 + sqrt_hi))
    dhi = qceil(2 / (2 * b + 1 + sqrt_lo))
    total_y = (u + v) / 2
    factor_y = 2 / dlo - 1
    ltlo, lthi = qlog_bounds(total_y)
    lflo, lfhi = qlog_bounds(factor_y)
    upper = qceil(lthi + lfhi + dhi - 1)
    slo, shi = dlo * (2 - dlo), dhi * (2 - dhi)
    base = 1 / (u + v)
    ru, rv = v * v / (2 * (u + v) ** 2), u * u / (2 * (u + v) ** 2)
    return {
        "u": u, "v": v, "x": x, "sqrt_lo": sqrt_lo, "sqrt_hi": sqrt_hi,
        "dlo": dlo, "dhi": dhi, "total_y": total_y, "factor_y": factor_y,
        "ltlo": ltlo, "lthi": lthi, "lflo": lflo, "lfhi": lfhi,
        "upper": upper,
        "gu_lo": base + slo * ru, "gu_hi": base + shi * ru,
        "gv_lo": base + slo * rv, "gv_hi": base + shi * rv,
    }


def qmul_upper(xlo: Q, xhi: Q, ylo: Q, yhi: Q) -> Q:
    return max(xlo * ylo, xlo * yhi, xhi * ylo, xhi * yhi)


def decimal_reference(z: Q, rl: Q, rh: Q, sl: Q, sh: Q) -> tuple[Q, Q, Q]:
    D = Decimal
    zD, rlD, rhD, slD, shD = map(q_to_decimal, (z, rl, rh, sl, sh))
    rflo, rfhi = max(rlD, 2 * slD - 1), min(rhD, 2 * shD / 3)
    r0 = (rflo + rfhi) / 2
    sflo, sfhi = max(slD, D("1.5") * r0), min(shD, (1 + r0) / 2)
    s0 = (sflo + sfhi) / 2

    def gu(u: Decimal, v: Decimal) -> Decimal:
        total = u + v
        b = u * v / (2 * total)
        delta = 2 / (2 * b + 1 + (4 * b * b + 1).sqrt())
        return 1 / total + delta * (2 - delta) * v * v / (2 * total * total)

    def aderiv(a: Decimal) -> Decimal:
        scale = 8 * zD
        return 4 * zD * (gu(scale * a, scale * (1 - s0)) -
                         gu(scale * (r0 - a), scale * (s0 - r0)))

    alo, ahi = max(D(0), 2 * r0 - s0), r0 / 2
    eps = D("1e-10")
    left, right = alo + eps, ahi - eps
    if left > right:
        a0 = (alo + ahi) / 2
    elif aderiv(left) <= 0:
        a0 = left
    elif aderiv(right) >= 0:
        a0 = right
    else:
        for _ in range(24):
            mid = (left + right) / 2
            if aderiv(mid) > 0:
                left = mid
            else:
                right = mid
        a0 = (left + right) / 2

    def rounded_inside(x: Decimal, lo: Decimal, hi: Decimal) -> Q:
        q = Q(round(x * SCALE), SCALE)
        loq, hiq = Q(str(lo)), Q(str(hi))
        return max(loq + Q(1, SCALE), min(hiq - Q(1, SCALE), q))

    r0q = rounded_inside(r0, rflo, rfhi)
    s0q = rounded_inside(s0, max(slD, D("1.5") * q_to_decimal(r0q)),
                        min(shD, (1 + q_to_decimal(r0q)) / 2))
    a0q = rounded_inside(a0, max(D(0), 2 * q_to_decimal(r0q) - q_to_decimal(s0q)),
                        q_to_decimal(r0q) / 2)
    return a0q, r0q, s0q


def matching_support(z: Q, rl: Q, rh: Q, sl: Q, sh: Q) -> tuple[Q, dict]:
    a0, r0, s0 = decimal_reference(z, rl, rh, sl, sh)
    k14 = kernel_jet(8 * z * a0, 8 * z * (1 - s0))
    k23 = kernel_jet(8 * z * (r0 - a0), 8 * z * (s0 - r0))
    ga = (4 * z * (k14["gu_lo"] - k23["gu_hi"]),
          4 * z * (k14["gu_hi"] - k23["gu_lo"]))
    gr = (4 * z * (k23["gu_lo"] - k23["gv_hi"]),
          4 * z * (k23["gu_hi"] - k23["gv_lo"]))
    gs = (4 * z * (-k14["gv_hi"] + k23["gv_lo"]),
          4 * z * (-k14["gv_lo"] + k23["gv_hi"]))
    alo, ahi = max(Q(0), 2 * rl - sh), rh / 2
    upper = ((k14["upper"] + k23["upper"]) / 2 +
             qmul_upper(*ga, alo - a0, ahi - a0) +
             qmul_upper(*gr, rl - r0, rh - r0) +
             qmul_upper(*gs, sl - s0, sh - s0))
    return upper, {"z": z, "a0": a0, "r0": r0, "s0": s0,
                   "k14": k14, "k23": k23, "upper": upper}


def q_to_decimal(x: Q) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)


def qjson(x):
    if isinstance(x, Q):
        return [x.numerator, x.denominator]
    if isinstance(x, dict):
        return {k: qjson(v) for k, v in x.items()}
    if isinstance(x, list):
        return [qjson(v) for v in x]
    return x


def run(target: Decimal, matching_floor: Decimal,
        output: str | None, nr: int, ns: int) -> None:
    D = Decimal
    th_lo, th_hi = Q("0.4086960373221888"), D("0.4086960373221890")
    zhi = Q("0.476")
    b_lo = D("0.8565576222695285")
    c2, ha, l2, l3 = D("0.009767"), D("0.031960"), D("0.011"), D("0.0468")
    alpha, c4, d4 = l3 - l2, D("0.09658"), D("0.49302")
    r20_up = (D("0.5").ln() * (b_lo + 2)).exp() + GUARD
    r30_up = (D("0.75").ln() * (b_lo + 2)).exp() + GUARD
    cbase = c2 + ha - l2 * r20_up.ln() - alpha * r30_up.ln()

    def endpoint_lower(z: Decimal) -> Decimal:
        if z <= th_hi:
            return D(0)
        return max(D(0), d4 * b_lo * (z - th_hi) -
                   d4 * d4 * (z - D("0.4086960373221888")) ** 2 / (4 * c4) - GUARD)

    def energy(z: Q, r: Q, s: Q) -> Decimal:
        zd, rd, sd = map(q_to_decimal, (z, r, s))
        ep = endpoint_lower(zd)
        val = cbase + ep + l2 * rd.ln() + alpha * sd.ln() + l3 * zd.ln() - GUARD
        return max(ep, val) - GUARD

    rlo, rhi, slo, shi = map(Q, ("0.05", "0.5", "0.075", "0.75"))
    dr, ds = (rhi - rlo) / nr, (shi - slo) / ns
    pending = deque((rlo + dr*i, rlo + dr*(i+1), slo + ds*j, slo + ds*(j+1), 0, f"{i}_{j}")
                    for i in range(nr) for j in range(ns))
    leaves = []
    checked = 0
    while pending:
        rl, rh, sl, sh, depth, path = pending.popleft()
        checked += 1
        if sh < Q(3, 2) * rl or sl > (1 + rh) / 2:
            leaves.append({"kind": "order", "box": [rl, rh, sl, sh], "path": path})
            continue
        up_hi, cert_hi = matching_support(zhi, rl, rh, sl, sh)
        if q_to_decimal(up_hi) < matching_floor:
            leaves.append({"kind": "matching", "box": [rl, rh, sl, sh], "path": path, "support": cert_hi})
            continue
        up_lo, cert_lo = matching_support(th_lo, rl, rh, sl, sh)
        if q_to_decimal(up_lo) >= matching_floor:
            zlo, cert = th_lo, None
        else:
            lo, hi, cert = th_lo, zhi, cert_lo
            for _ in range(10):
                mid = (lo + hi) / 2
                up, midcert = matching_support(mid, rl, rh, sl, sh)
                if q_to_decimal(up) < matching_floor:
                    lo, cert = mid, midcert
                else:
                    hi = mid
            zlo = lo
        if q_to_decimal(sl * zlo) / r30_up > D("0.66"):
            leaves.append({"kind": "tail", "box": [rl, rh, sl, sh], "path": path,
                           "zlo": zlo, "support": cert})
            continue
        e_q = qcentral_energy(zlo, rl, sl)
        e = q_to_decimal(e_q)
        if e_q > Q(str(target)):
            leaves.append({"kind": "energy", "box": [rl, rh, sl, sh], "path": path,
                           "zlo": zlo, "support": cert, "energy": str(e)})
            continue
        if depth >= 28:
            raise RuntimeError(f"unresolved depth {depth}: {(rl,rh,sl,sh)}, {zlo}, {e}")
        score_r = l2 * q_to_decimal(rh - rl) / q_to_decimal(rl)
        score_s = alpha * q_to_decimal(sh - sl) / q_to_decimal(sl)
        if score_r >= score_s:
            mid = (rl + rh) / 2
            pending.append((rl, mid, sl, sh, depth + 1, path + "0"))
            pending.append((mid, rh, sl, sh, depth + 1, path + "1"))
        else:
            mid = (sl + sh) / 2
            pending.append((rl, rh, sl, mid, depth + 1, path + "0"))
            pending.append((rl, rh, mid, sh, depth + 1, path + "1"))
        if checked % 1000 == 0:
            print("checked", checked, "pending", len(pending), "leaves", len(leaves), flush=True)
    counts = {k: sum(x["kind"] == k for x in leaves)
              for k in ("order", "matching", "tail", "energy")}
    print("target", target, "matching_floor", matching_floor,
          "checked", checked, "leaves", len(leaves), "counts", counts)
    if output:
        with open(output, "w", encoding="utf-8") as f:
            json.dump({"target": str(target), "matching_floor": str(matching_floor),
                       "checked": checked, "counts": counts,
                       "leaves": qjson(leaves)}, f, separators=(",", ":"))
        print("wrote", output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", default="0.0201")
    parser.add_argument("--matching-floor", default="0")
    parser.add_argument("--output")
    parser.add_argument("--nr", type=int, default=28)
    parser.add_argument("--ns", type=int, default=36)
    args = parser.parse_args()
    with localcontext() as ctx:
        ctx.prec = 70
        run(Decimal(args.target), Decimal(args.matching_floor),
            args.output, args.nr, args.ns)
