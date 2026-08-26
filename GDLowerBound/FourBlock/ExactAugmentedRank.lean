import GDLowerBound.FourBlock.ExactAugmentedPath

/-!
# Exact augmented endpoint theorem indexed directly by the rank

The path proof is naturally parameterized by `n` with rank `n+1`.  Schedule
weights also carry a proof that the rank is admissible, so rewriting
`(q-1)+1=q` directly creates dependent proof terms.  We transport the whole
statement through the subtype of admissible ranks instead.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

theorem topChain_reciprocalProduct_le_exactAugmentedPath_rank
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq2 : 2 ≤ q) (hq : q ≤ longCount h) :
    (topChain h q).terminalScale *
        ∏ i : Fin q, (chronologicalLocalBound h q hq i)⁻¹ ≤
      (4 * unresolvedMass h q * (q - 1) / q) *
        chronologicalEdgeKernelProduct (topPathWeight h q hq) := by
  have hn : 0 < q - 1 := by omega
  have hq' : (q - 1) + 1 ≤ longCount h := by omega
  have hbase := topChain_reciprocalProduct_le_exactAugmentedPath
    (h := h) hh hn hq'
  let Rank := {r : ℕ // r ≤ longCount h}
  let x : Rank := ⟨(q - 1) + 1, hq'⟩
  let y : Rank := ⟨q, hq⟩
  let P : Rank → Prop := fun s ↦
    (topChain h s.1).terminalScale *
        ∏ i : Fin s.1,
          (chronologicalLocalBound h s.1 s.2 i)⁻¹ ≤
      (4 * unresolvedMass h s.1 * (s.1 - 1) / s.1) *
        chronologicalEdgeKernelProduct (topPathWeight h s.1 s.2)
  have hx : P x := by
    dsimp only [P, x]
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)] at hbase ⊢
    exact hbase
  have hxy : x = y := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hy : P y := hxy ▸ hx
  exact hy

end

end GDLowerBound.FourBlock
