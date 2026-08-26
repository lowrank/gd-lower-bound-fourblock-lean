"""Size/tightness experiment for the Lean rational support checker.

This is an untrusted certificate generator: every bound it computes is
recomputed over `Rat` by Lean.  It mirrors `qMatchingSupportUpper` exactly.
"""

from decimal import Decimal, localcontext
from fractions import Fraction as Q


def qsqrt_upper(x: Q, n: int) -> Q:
    u = (x + 1) / 2
    for _ in range(n):
        u = (u + x / u) / 2
    return u


def qlog_upper(y: Q, n: int) -> Q:
    x = (y - 1) / (y + 1)
    series = sum((x ** (2 * i + 1) / (2 * i + 1) for i in range(n)), Q(0))
    error = abs(x) ** (2 * n + 1) / (1 - x * x)
    return 2 * (series + error)


def qedge(u: Q, v: Q) -> Q:
    return u * v / (2 * (u + v))


def qdelta_lower(b: Q, sqrt_steps: int) -> Q:
    return 2 / (2 * b + 1 + qsqrt_upper(4 * b * b + 1, sqrt_steps))


def qslope_bounds(b: Q, sqrt_steps: int) -> tuple[Q, Q]:
    dlo = qdelta_lower(b, sqrt_steps)
    dhi = 1 / (b + 1)
    return dlo * (2 - dlo), dhi * (2 - dhi)


def qkernel_upper(u: Q, v: Q, sqrt_steps: int, log_steps: int) -> Q:
    b = qedge(u, v)
    dlo = qdelta_lower(b, sqrt_steps)
    dhi = 1 / (b + 1)
    return qlog_upper((u + v) / 2, log_steps) + qlog_upper(2 / dlo - 1, log_steps) + dhi - 1


def qkernel_grad_bounds(u: Q, v: Q, sqrt_steps: int) -> tuple[tuple[Q, Q], tuple[Q, Q]]:
    slo, shi = qslope_bounds(qedge(u, v), sqrt_steps)
    base = 1 / (u + v)
    ru = v * v / (2 * (u + v) ** 2)
    rv = u * u / (2 * (u + v) ** 2)
    return (base + slo * ru, base + shi * ru), (base + slo * rv, base + shi * rv)


def qmul_upper(xlo: Q, xhi: Q, ylo: Q, yhi: Q) -> Q:
    return max(xlo * ylo, xlo * yhi, xhi * ylo, xhi * yhi)


def qmatching_support(z: Q, a0: Q, r0: Q, s0: Q,
                      alo: Q, ahi: Q, rlo: Q, rhi: Q, slo: Q, shi: Q,
                      sqrt_steps: int, log_steps: int) -> Q:
    u14, v14 = 8 * z * a0, 8 * z * (1 - s0)
    u23, v23 = 8 * z * (r0 - a0), 8 * z * (s0 - r0)
    h0 = (qkernel_upper(u14, v14, sqrt_steps, log_steps) +
          qkernel_upper(u23, v23, sqrt_steps, log_steps)) / 2
    (gu14, gv14) = qkernel_grad_bounds(u14, v14, sqrt_steps)
    (gu23, gv23) = qkernel_grad_bounds(u23, v23, sqrt_steps)
    ga = (4 * z * (gu14[0] - gu23[1]), 4 * z * (gu14[1] - gu23[0]))
    gr = (4 * z * (gu23[0] - gv23[1]), 4 * z * (gu23[1] - gv23[0]))
    gs = (4 * z * (-gv14[1] + gv23[0]), 4 * z * (-gv14[0] + gv23[1]))
    return (h0 + qmul_upper(*ga, alo - a0, ahi - a0) +
            qmul_upper(*gr, rlo - r0, rhi - r0) +
            qmul_upper(*gs, slo - s0, shi - s0))


def as_q(x: Decimal) -> Q:
    return Q(str(x))


def as_d(x: Q) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)


def decimal_matching_reference(z: Decimal, rl: Decimal, rh: Decimal,
                               sl: Decimal, sh: Decimal) -> tuple[Decimal, Decimal, Decimal]:
    z0, one, two = Decimal(0), Decimal(1), Decimal(2)
    rflo, rfhi = max(rl, two * sl - one), min(rh, two * sh / Decimal(3))
    r0 = (rflo + rfhi) / two
    sflo, sfhi = max(sl, Decimal("1.5") * r0), min(sh, (one + r0) / two)
    s0 = (sflo + sfhi) / two

    def deriv(a: Decimal) -> Decimal:
        def gu(u: Decimal, v: Decimal) -> Decimal:
            total = u + v
            b = u * v / (two * total)
            d = two / (two * b + one + (4 * b * b + one).sqrt())
            return one / total + d * (two - d) * v * v / (two * total * total)
        scale = 8 * z
        return 4 * z * (gu(scale * a, scale * (one - s0)) -
                        gu(scale * (r0 - a), scale * (s0 - r0)))

    alo, ahi = max(z0, two * r0 - s0), r0 / two
    eps = Decimal("1e-25")
    left, right = min(ahi, alo + eps), max(alo, ahi - eps)
    if deriv(left) <= 0:
        a0 = left
    elif deriv(right) >= 0:
        a0 = right
    else:
        for _ in range(24):
            mid = (left + right) / two
            if deriv(mid) > 0:
                left = mid
            else:
                right = mid
        a0 = (left + right) / two
    return a0, r0, s0


if __name__ == "__main__":
    with localcontext() as ctx:
        ctx.prec = 60
        samples = [
            (Decimal("0.4086960373221888"), Decimal("0.20"), Decimal("0.22"), Decimal("0.36"), Decimal("0.39")),
            (Decimal("0.44"), Decimal("0.30"), Decimal("0.32"), Decimal("0.48"), Decimal("0.51")),
            (Decimal("0.47"), Decimal("0.44"), Decimal("0.46"), Decimal("0.68"), Decimal("0.71")),
        ]
        for z, rl, rh, sl, sh in samples:
            a0, r0, s0 = decimal_matching_reference(z, rl, rh, sl, sh)
            alo, ahi = max(Decimal(0), 2 * rl - sh), rh / 2
            print("sample", z, (rl, rh, sl, sh), "ref", (a0, r0, s0))
            for sn, ln in [(3, 10), (4, 12), (5, 16)]:
                upper = qmatching_support(*(as_q(x) for x in
                    (z, a0, r0, s0, alo, ahi, rl, rh, sl, sh)), sn, ln)
                print("  steps", sn, ln, "upper", as_d(upper),
                      "bits", upper.numerator.bit_length(), upper.denominator.bit_length())
