"""Convert untrusted central-certificate JSON into compact Lean data."""

import argparse
from fractions import Fraction as Q
import json


def q(x) -> Q:
    return Q(x[0], x[1])


def qlean(x) -> str:
    x = q(x) if isinstance(x, list) else x
    if x.denominator == 1:
        return str(x.numerator)
    if x.numerator < 0:
        return f"(-{-x.numerator} / {x.denominator})"
    return f"({x.numerator} / {x.denominator})"


def kernel_witness(k: dict) -> str:
    return ("{ sqrtLower := " + qlean(k["sqrt_lo"]) +
            ", sqrtUpper := " + qlean(k["sqrt_hi"]) +
            ", deltaLower := " + qlean(k["dlo"]) +
            ", deltaUpper := " + qlean(k["dhi"]) +
            ", logTotalUpper := " + qlean(k["lthi"]) +
            ", logFactorUpper := " + qlean(k["lfhi"]) + " }")


def matching_witness(c: dict) -> str:
    return ("{ z := " + qlean(c["z"]) +
            ", a₀ := " + qlean(c["a0"]) +
            ", r₀ := " + qlean(c["r0"]) +
            ", s₀ := " + qlean(c["s0"]) +
            ", w14 := " + kernel_witness(c["k14"]) +
            ", w23 := " + kernel_witness(c["k23"]) + " }")


class Node:
    def __init__(self):
        self.children = {}
        self.leaf = None


def insert(root: Node, path: str, leaf: dict):
    node = root
    for bit in path:
        node = node.children.setdefault(bit, Node())
    if node.leaf is not None or node.children:
        raise ValueError("certificate paths are not prefix-free")
    node.leaf = leaf


def bbox(node: Node):
    if node.leaf is not None:
        return tuple(q(x) for x in node.leaf["box"])
    bs = [bbox(node.children[b]) for b in "01"]
    return (min(x[0] for x in bs), max(x[1] for x in bs),
            min(x[2] for x in bs), max(x[3] for x in bs))


def emit_leaf(leaf: dict, indent: int) -> str:
    kind = leaf["kind"]
    if kind == "order":
        return ".leaf .order"
    if kind == "matching":
        return ".leaf (.matching " + matching_witness(leaf["support"]) + ")"
    if kind == "energy":
        support = leaf["support"]
        support_text = "none" if support is None else "(some " + matching_witness(support) + ")"
        return ".leaf (.energy " + qlean(leaf["zlo"]) + " " + support_text + ")"
    raise ValueError(f"unsupported central leaf kind {kind}")


def emit_tree_raw(node: Node, emit_child, indent: int = 2, level: int = 0) -> str:
    if node.leaf is not None:
        return emit_leaf(node.leaf, indent)
    if set(node.children) != {"0", "1"}:
        raise ValueError("internal node does not have two children")
    left, right = node.children["0"], node.children["1"]
    bl, br = bbox(left), bbox(right)
    if bl[1] == br[0] and bl[2] == br[2] and bl[3] == br[3]:
        ctor, mid = ".splitR", bl[1]
    elif bl[3] == br[2] and bl[0] == br[0] and bl[1] == br[1]:
        ctor, mid = ".splitS", bl[3]
    else:
        raise ValueError(f"children do not form a coordinate split: {bl}, {br}")
    pad = " " * indent
    return (f"{ctor} {qlean(mid)}\n{pad}  ({emit_child(left, indent + 2, level + 1)})\n"
            f"{pad}  ({emit_child(right, indent + 2, level + 1)})")


def emit_chunked_tree(root: Node, cutoff: int = 5):
    definitions = []
    counter = 0

    def make_chunk(node: Node) -> str:
        nonlocal counter
        name = f"centralCertificateChunk{counter}"
        counter += 1
        expr = emit_node(node, 2, 0)
        definitions.append((name, expr))
        return name

    def emit_node(node: Node, indent: int, level: int) -> str:
        if node.leaf is not None:
            return emit_leaf(node.leaf, indent)
        if level >= cutoff:
            return make_chunk(node)
        return emit_tree_raw(node, emit_node, indent, level)

    root_expr = emit_node(root, 2, 0)
    return definitions, root_expr


def main(input_path: str, output_path: str):
    with open(input_path, encoding="utf-8") as f:
        data = json.load(f)
    root = Node()
    for leaf in data["leaves"]:
        path = leaf["path"]
        if not path.startswith("0_0"):
            raise ValueError(f"unexpected root tag: {path}")
        insert(root, path[3:], leaf)
    chunks, tree = emit_chunked_tree(root)
    chunk_text = "\n\n".join(f"def {name} : CentralCertTree :=\n  {expr}" for name, expr in chunks)
    text = """import GDLowerBound.FourBlock.CentralTreeChecker

/-! This file is generated data.  Its only trusted fact is the theorem
`centralCertificate_valid`, proved by evaluation inside Lean. -/

namespace GDLowerBound.FourBlock

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def centralCertificateBox : CentralQBox :=
  { rlo := 1 / 20, rhi := 1 / 2, slo := 3 / 40, shi := 3 / 4 }

""" + chunk_text + """


def centralCertificate : CentralCertTree :=
  """ + tree + """

theorem centralCertificate_valid :
    CentralCertTree.valid centralCertificate centralCertificateBox = true := by
  native_decide

theorem certifiedCentralEnergy {z a r s : ℝ}
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s)
    (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ)) :
    31 / 1250 < centralEnergy z r s := by
  have hmem : centralCertificateBox.Mem r s := by
    dsimp only [centralCertificateBox, CentralQBox.Mem]
    push_cast
    exact ⟨hrlo, hrhi, hslo, hshi⟩
  exact CentralCertTree.sound (tree := centralCertificate) (b := centralCertificateBox)
    centralCertificate_valid hz0 hzlo hzhi ha h2 h3 h4 hord hmatch hmem

end GDLowerBound.FourBlock
"""
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    args = parser.parse_args()
    main(args.input, args.output)
