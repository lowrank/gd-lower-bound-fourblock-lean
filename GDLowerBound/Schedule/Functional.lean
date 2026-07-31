import GDLowerBound.Schedule.Chain
import Mathlib.Data.Finset.Lattice.Fold

namespace GDLowerBound.Schedule

open scoped BigOperators

namespace Chain

variable {T : ℕ} {h : StepSchedule T}

/-- The terminal contribution associated with a chronological chain when
every local amplitude constraint is saturated. -/
noncomputable def value (c : Chain h) : ℝ :=
  c.terminalScale⁻¹ * ∏ i, c.localBound i

theorem value_pos (c : Chain h) (hh : IsNonnegativeSchedule h) :
    0 < c.value := by
  unfold value
  exact mul_pos (inv_pos.mpr (c.terminalScale_pos hh))
    (Finset.prod_pos fun i _ ↦ c.localBound_pos hh i)

theorem value_nonneg (c : Chain h) (hh : IsNonnegativeSchedule h) :
    0 ≤ c.value := (c.value_pos hh).le

@[simp]
theorem value_empty :
    (empty h).value = (1 + 2 * ∑ t, h t)⁻¹ := by
  unfold value
  rw [terminalScale_empty]
  have hprod : ∏ i : Fin (empty h).length, (empty h).localBound i = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact Fin.elim0 (Fin.cast length_empty i)
  rw [hprod, mul_one]

end Chain

/-- There are only finitely many admissible chains. -/
noncomputable instance chainFintype {T : ℕ} (h : StepSchedule T) :
    Fintype (Chain h) :=
  Fintype.ofInjective (fun c : Chain h ↦ c.times) fun _ _ hcd ↦ Chain.ext hcd

private theorem allChains_nonempty {T : ℕ} (h : StepSchedule T) :
    (Finset.univ : Finset (Chain h)).Nonempty :=
  ⟨Chain.empty h, Finset.mem_univ _⟩

/-- The normalized lower-bound functional `ᶜ_T(h)`, including the empty
chain. -/
noncomputable def lowerBoundFunctional {T : ℕ} (h : StepSchedule T) : ℝ :=
  (Finset.univ : Finset (Chain h)).sup' (allChains_nonempty h) Chain.value

theorem chainValue_le_functional {T : ℕ} (h : StepSchedule T)
    (c : Chain h) : c.value ≤ lowerBoundFunctional h := by
  exact Finset.le_sup' Chain.value (Finset.mem_univ c)

theorem emptyValue_le_functional {T : ℕ} (h : StepSchedule T) :
    (1 + 2 * ∑ t, h t)⁻¹ ≤ lowerBoundFunctional h := by
  rw [← Chain.value_empty]
  exact chainValue_le_functional h (Chain.empty h)

theorem lowerBoundFunctional_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) : 0 < lowerBoundFunctional h :=
  (Chain.value_pos (Chain.empty h) hh).trans_le
    (chainValue_le_functional h (Chain.empty h))

/-- The maximum defining `ᶜ_T(h)` is attained, including when the empty
chain is the maximizer. -/
theorem exists_maximizingChain {T : ℕ} (h : StepSchedule T) :
    ∃ c : Chain h, lowerBoundFunctional h = c.value := by
  obtain ⟨c, hc, hvalue⟩ :=
    Finset.exists_mem_eq_sup' (allChains_nonempty h) Chain.value
  exact ⟨c, hvalue⟩

end GDLowerBound.Schedule
