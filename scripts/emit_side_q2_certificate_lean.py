"""Generate and emit the exact-rational one-dimensional Q2 certificate."""

import argparse
from collections import deque
from fractions import Fraction as Q

from generate_fourblock_compact_certificate import qlog_exact


THLO = Q("0.4086960373221888")
THHI = Q("0.4086960373221890")
BLO = Q("0.8565576222695285")
BHI = Q("0.8565576222695288")
C2 = Q("0.04")
D2 = Q("0.0188")
L2 = Q("0.011")
K2LO = D2 + BLO * L2
K2HI = D2 + BHI * L2


def scale(y):
    return 4 if y < Q(1, 8) else 3 if y < Q(1, 4) else 2 if y < Q(1, 2) else 1


def qscaled_log_upper(y):
    k = scale(y)
    return qlog_exact(y * 2**k)[1] - k * qlog_exact(Q(2))[0]


def lower(zl, zh):
    dzlo = max(Q(0), zl - THHI)
    dzhi = max(Q(0), zh - THLO)
    return (K2LO * BLO * dzlo - K2HI**2 * dzhi**2 / (4 * C2)
            - L2 * qscaled_log_upper(zh))


class Node:
    def __init__(self):
        self.children = {}
        self.box = None


def qlean(x):
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator})"


def generate(target, max_depth):
    root = Node()
    pending = deque([(THLO, Q("2.90"), 0, "")])
    leaves = checked = depth_seen = 0
    while pending:
        zl, zh, depth, path = pending.popleft()
        checked += 1
        if lower(zl, zh) > target:
            node = root
            for bit in path:
                node = node.children.setdefault(bit, Node())
            node.box = (zl, zh)
            leaves += 1
            depth_seen = max(depth_seen, depth)
            continue
        if depth >= max_depth:
            raise RuntimeError((zl, zh, lower(zl, zh)))
        mid = (zl + zh) / 2
        pending.append((zl, mid, depth + 1, path + "0"))
        pending.append((mid, zh, depth + 1, path + "1"))
    print("checked", checked, "leaves", leaves, "depth", depth_seen)
    return root


def bbox(node):
    if node.box is not None:
        return node.box
    left, right = node.children["0"], node.children["1"]
    return bbox(left)[0], bbox(right)[1]


def chunked(root, prefix, cutoff=5):
    defs = []
    counter = 0

    def chunk(node):
        nonlocal counter
        name = f"{prefix}Chunk{counter}"
        counter += 1
        defs.append((name, emit(node, 0)))
        return name

    def emit(node, level):
        if node.box is not None:
            return ".leaf"
        if level >= cutoff:
            return chunk(node)
        left, right = node.children["0"], node.children["1"]
        mid = bbox(left)[1]
        if mid != bbox(right)[0]:
            raise ValueError("non-adjacent children")
        return f".split {qlean(mid)}\n    ({emit(left, level + 1)})\n    ({emit(right, level + 1)})"

    return defs, emit(root, 0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("output")
    parser.add_argument("--target", type=Q, default=Q("0.009767"))
    parser.add_argument("--max-depth", type=int, default=60)
    args = parser.parse_args()
    root = generate(args.target, args.max_depth)
    chunks, tree = chunked(root, "sideQ2Certificate")
    chunk_text = "\n\n".join(
        f"def {name} : SideQ2Tree :=\n  {expr}" for name, expr in chunks)
    target = qlean(args.target)
    text = f"""import GDLowerBound.FourBlock.SideQ2Checker

/-! Generated Q2 data.  Its validity is recomputed over exact rationals. -/

namespace GDLowerBound.FourBlock

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sideQ2CertificateTarget : ℚ := {target}
def sideQ2CertificateBox : SideQ2Box :=
  {{ zlo := {qlean(THLO)}, zhi := {qlean(Q('2.90'))} }}

{chunk_text}

def sideQ2Certificate : SideQ2Tree :=
  {tree}

theorem sideQ2Certificate_valid :
    SideQ2Tree.valid sideQ2CertificateTarget sideQ2Certificate
      sideQ2CertificateBox = true := by
  native_decide

theorem sideQ2Certificate_sound {{z v : ℝ}}
    (hz : criticalTheta ≤ z) (hzlo : ({qlean(THLO)} : ℝ) ≤ z)
    (hzhi : z ≤ ({qlean(Q('2.90'))} : ℝ)) :
    ({target} : ℝ) < sideQ2 z v := by
  have hmem : sideQ2CertificateBox.Mem z := by
    dsimp only [sideQ2CertificateBox, SideQ2Box.Mem]
    push_cast
    exact ⟨hzlo, hzhi⟩
  simpa [sideQ2CertificateTarget] using
    (SideQ2Tree.sound (tree := sideQ2Certificate) (b := sideQ2CertificateBox)
      sideQ2Certificate_valid hz hmem (v := v))

end GDLowerBound.FourBlock
"""
    with open(args.output, "w", encoding="utf-8") as stream:
        stream.write(text)
