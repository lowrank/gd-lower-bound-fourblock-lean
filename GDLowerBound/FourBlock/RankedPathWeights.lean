import GDLowerBound.FourBlock.SortedInsertion
import Mathlib.Data.List.NodupEquivFin

/-!
# Exact ranked form of the internal endpoint-path weights

The endpoint path stores the selected excesses in chronological order,
whereas the four-block coordinates use rank order.  This module constructs
the exact permutation between these orders and proves that sorting the
internal path weights gives the scaled reciprocal-rank tuple.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

noncomputable def rankedTopEquiv {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) : Fin q ≃ ↑(topTimes h q) :=
  let l := (rankedTimes h).take q
  let hlen : l.length = q := List.length_take_of_le (by
    simpa only [rankedTimes_length] using hq)
  (Fin.castOrderIso hlen.symm).toEquiv |>.trans
    (List.Nodup.getEquiv l (rankedTimes_nodup h).take) |>.trans
      (Equiv.subtypeEquivProp (by
        funext t
        apply propext
        exact (mem_topTimes_iff h q t).symm))

noncomputable def chronologicalTopEquiv {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) : Fin q ≃ ↑(topTimes h q) :=
  let c := topChain h q
  let hlen : c.length = q := topChain_length_of_le h hq
  (Fin.castOrderIso hlen.symm).toEquiv |>.trans
    (Schedule.Chain.selectedEquiv c) |>.trans
      (Equiv.subtypeEquivProp (by rfl))

/-- Permutation sending a chronological top-chain index to the index of the
same schedule time in decreasing-excess rank order. -/
noncomputable def chronologicalToRank {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) : Equiv.Perm (Fin q) :=
  (chronologicalTopEquiv h hq).trans (rankedTopEquiv h hq).symm

theorem rankedTopEquiv_excess {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) (i : Fin q) :
    excess h (rankedTopEquiv h hq i) = rankedExcessOne h (i.val + 1) := by
  unfold rankedTopEquiv rankedExcessOne
  change excess h (((rankedTimes h).take q).get
      ⟨i.val, by simp [rankedTimes_length, hq]⟩) = _
  rw [List.get_eq_getElem, List.getElem_take]
  unfold rankedExcesses
  rw [List.getD_eq_getElem]
  all_goals simp [rankedTimes_length] <;> omega

theorem chronologicalTopEquiv_excess {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) (i : Fin q) :
    excess h (chronologicalTopEquiv h hq i) =
      chronologicalExcess h q hq i := by
  rfl

/-- Chronological excesses are exactly the ranked excesses after applying
the explicit order permutation. -/
theorem chronologicalExcess_eq_ranked
    {T q : ℕ} (h : StepSchedule T) (hq : q ≤ longCount h) (i : Fin q) :
    chronologicalExcess h q hq i =
      rankedExcessOne h ((chronologicalToRank h hq i).val + 1) := by
  let j := chronologicalToRank h hq i
  have hsame : rankedTopEquiv h hq j = chronologicalTopEquiv h hq i := by
    simp [j, chronologicalToRank]
  rw [← rankedTopEquiv_excess h hq j,
    hsame, chronologicalTopEquiv_excess]

/-- Rank-ordered scaled reciprocal weights at a general cutoff. -/
def rankedPathWeights {T q : ℕ} (h : StepSchedule T) : Fin q → ℝ :=
  fun i ↦ 2 * unresolvedMass h q / q *
    (rankedExcessOne h (i.val + 1))⁻¹

/-- The genuine (non-auxiliary) endpoint-path weights in chronological
order. -/
def topPathInternalWeights {T q : ℕ} (h : StepSchedule T)
    (hq : q ≤ longCount h) : Fin q → ℝ :=
  fun i ↦ topPathWeight h q hq i.castSucc

theorem topPathInternalWeights_eq_comp
    {T q : ℕ} (h : StepSchedule T) (hq0 : 0 < q)
    (hq : q ≤ longCount h) :
    topPathInternalWeights h hq =
      rankedPathWeights h ∘ chronologicalToRank h hq := by
  funext i
  unfold topPathInternalWeights rankedPathWeights
  rw [topPathWeight_castSucc h hq0 hq i,
    chronologicalExcess_eq_ranked]
  rfl

theorem rankedPathWeights_monotone
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) :
    Monotone (rankedPathWeights (q := q) h) := by
  intro i j hij
  have hi := rankedExcessOne_pos h (q := i.val + 1) (by omega) (by omega)
  have hj := rankedExcessOne_pos h (q := j.val + 1) (by omega) (by omega)
  have hanti := rankedExcessOne_antitone h
    (a := i.val + 1) (b := j.val + 1) (by omega) (by omega) (by omega)
  have hinv : (rankedExcessOne h (i.val + 1))⁻¹ ≤
      (rankedExcessOne h (j.val + 1))⁻¹ :=
    (inv_le_inv₀ hi hj).2 hanti
  unfold rankedPathWeights
  have hscale : 0 ≤ 2 * unresolvedMass h q / (q : ℝ) := by
    positivity [unresolvedMass_pos hh q]
  exact mul_le_mul_of_nonneg_left hinv hscale

/-- Sorting removes the chronological order and produces the rank-ordered
scaled reciprocal tuple exactly. -/
theorem sortedWeight_topPathInternalWeights_eq_rankedPathWeights
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) :
    sortedWeight (topPathInternalWeights h hq) = rankedPathWeights h := by
  let σ := chronologicalToRank h hq
  have hinter := topPathInternalWeights_eq_comp h hq0 hq
  have hperm := Tuple.comp_perm_comp_sort_eq_comp_sort
    (f := rankedPathWeights (q := q) h) (σ := σ)
  have hsort : Tuple.sort (rankedPathWeights (q := q) h) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr
      (rankedPathWeights_monotone (q := q) hh hq0 hq)
  unfold sortedWeight
  rw [hinter]
  rw [hsort] at hperm
  simpa only [σ, Equiv.coe_refl, Function.comp_id] using hperm

/-- At cutoff `4m`, the ranked path tuple is a common positive scale times
the ideal reciprocal tuple. -/
theorem rankedPathWeights_fourBlock_eq
    {T m : ℕ} (h : StepSchedule T) :
    rankedPathWeights (q := 2 * (m + m)) h = fun i ↦
      (2 * unresolvedMass h (2 * (m + m)) / (2 * (m + m) : ℕ)) *
        idealReciprocalWeights h m i := by
  rfl

end

end GDLowerBound.FourBlock
