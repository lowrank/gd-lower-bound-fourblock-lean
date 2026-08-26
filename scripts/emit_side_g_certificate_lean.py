"""Convert untrusted side-G JSON trees into Lean data checked by native_decide."""

import argparse
from fractions import Fraction as Q
import json


def q(x):
    return Q(x[0], x[1])


def qlean(x):
    x = q(x) if isinstance(x, list) else x
    if x.denominator == 1:
        return str(x.numerator)
    if x.numerator < 0:
        return f"(-{-x.numerator} / {x.denominator})"
    return f"({x.numerator} / {x.denominator})"


class Node:
    def __init__(self):
        self.children = {}
        self.leaf = None


def insert(root, path, leaf):
    node = root
    for bit in path:
        node = node.children.setdefault(bit, Node())
    if node.leaf is not None or node.children:
        raise ValueError("certificate paths are not prefix-free")
    node.leaf = leaf


def bbox(node):
    if node.leaf is not None:
        return tuple(q(x) for x in node.leaf["box"])
    boxes = [bbox(node.children[b]) for b in "01"]
    return (min(x[0] for x in boxes), max(x[1] for x in boxes),
            min(x[2] for x in boxes), max(x[3] for x in boxes))


def emit_leaf(leaf):
    return ".leaf ." + leaf["kind"]


def emit_chunked(root, prefix, cutoff=5):
    definitions = []
    counter = 0

    def make_chunk(node):
        nonlocal counter
        name = f"{prefix}Chunk{counter}"
        counter += 1
        definitions.append((name, emit_node(node, 0)))
        return name

    def emit_node(node, level):
        if node.leaf is not None:
            return emit_leaf(node.leaf)
        if level >= cutoff:
            return make_chunk(node)
        if set(node.children) != {"0", "1"}:
            raise ValueError("internal node does not have two children")
        left, right = node.children["0"], node.children["1"]
        bl, br = bbox(left), bbox(right)
        if bl[1] == br[0] and bl[2] == br[2] and bl[3] == br[3]:
            ctor, mid = ".splitZ", bl[1]
        elif bl[3] == br[2] and bl[0] == br[0] and bl[1] == br[1]:
            ctor, mid = ".splitV", bl[3]
        else:
            raise ValueError(f"children do not form a coordinate split: {bl}, {br}")
        return f"{ctor} {qlean(mid)}\n    ({emit_node(left, level + 1)})\n    ({emit_node(right, level + 1)})"

    tree = emit_node(root, 0)
    return definitions, tree


def load(path, prefix):
    with open(path, encoding="utf-8") as stream:
        data = json.load(stream)
    root = Node()
    for leaf in data["leaves"]:
        insert(root, leaf["path"], leaf)
    chunks, tree = emit_chunked(root, prefix)
    return data, chunks, tree


def certificate_text(data, chunks, tree, prefix):
    root = data["root"]
    qmax, target = q(data["qmax"]), q(data["target"])
    chunk_text = "\n\n".join(
        f"def {name} : SideGTree :=\n  {expr}" for name, expr in chunks)
    return f"""
def {prefix}Qmax : ℚ := {qlean(qmax)}
def {prefix}Target : ℚ := {qlean(target)}
def {prefix}Box : SideGBox :=
  {{ zlo := {qlean(root[0])}, zhi := {qlean(root[1])},
    vlo := {qlean(root[2])}, vhi := {qlean(root[3])} }}

{chunk_text}

def {prefix} : SideGTree :=
  {tree}

theorem {prefix}_valid :
    SideGTree.valid {prefix}Qmax {prefix}Target {prefix} {prefix}Box = true := by
  native_decide

theorem {prefix}_sound {{z v : ℝ}}
    (hz : criticalTheta ≤ z) (hzlo : ({qlean(root[0])} : ℝ) ≤ z)
    (hzhi : z ≤ ({qlean(root[1])} : ℝ)) (hv0 : 0 ≤ v)
    (hvhi : v ≤ ({qlean(root[3])} : ℝ)) (hvz : v ≤ 1 / z)
    (hconstraint : Real.log z - betaLower * v * (z - criticalTheta) ≤
      Real.log ({qlean(qmax)} : ℝ)) :
    ({qlean(target)} : ℝ) < sideG z v := by
  have hz0 : 0 < z := criticalTheta_pos.trans_le hz
  have hmem : {prefix}Box.Mem z v := by
    dsimp only [{prefix}Box, SideGBox.Mem]
    push_cast
    exact ⟨hzlo, hzhi, hv0, hvhi⟩
  simpa [{prefix}Target] using SideGTree.sound (tree := {prefix}) (b := {prefix}Box)
    {prefix}_valid (by norm_num [{prefix}Qmax]) hz0 hz hv0 hvz
      (by simpa [{prefix}Qmax] using hconstraint) hmem
"""


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("q66")
    parser.add_argument("q82")
    parser.add_argument("output")
    args = parser.parse_args()
    d66, c66, t66 = load(args.q66, "sideG66Certificate")
    d82, c82, t82 = load(args.q82, "sideG82Certificate")
    text = """import GDLowerBound.FourBlock.SideGChecker

/-! Generated certificate data.  The search scripts are untrusted; the two
validity theorems are evaluated by Lean over exact rationals. -/

namespace GDLowerBound.FourBlock

set_option maxHeartbeats 0
set_option maxRecDepth 100000
"""
    text += certificate_text(d66, c66, t66, "sideG66Certificate")
    text += certificate_text(d82, c82, t82, "sideG82Certificate")
    text += "\nend GDLowerBound.FourBlock\n"
    with open(args.output, "w", encoding="utf-8") as stream:
        stream.write(text)
