import GDLowerBound.FourBlock.CoupledEqualization

/-! # Four-block coordinates and their exact ordered domain -/

namespace GDLowerBound.FourBlock

noncomputable section

/-- The four quarter-block masses `(a, r-a, s-r, 1-s)` are nonnegative and
nondecreasing. -/
def OrderedFourBlocks (a r s : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ r - a ∧ r - a ≤ s - r ∧ s - r ≤ 1 - s

theorem orderedFourBlocks_domain {a r s : ℝ}
    (h : OrderedFourBlocks a r s) :
    0 ≤ r ∧ r ≤ 1 / 2 ∧ 3 * r / 2 ≤ s ∧ s ≤ (1 + r) / 2 ∧
      max 0 (2 * r - s) ≤ a ∧ a ≤ r / 2 := by
  rcases h with ⟨ha0, h12, h23, h34⟩
  have hr0 : 0 ≤ r := by linarith
  have har : 2 * r - s ≤ a := by linarith
  constructor
  · exact hr0
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact max_le ha0 har
  · linarith

theorem orderedFourBlocks_of_domain {a r s : ℝ}
    (ha : max 0 (2 * r - s) ≤ a) (har : a ≤ r / 2)
    (hs : s ≤ (1 + r) / 2) : OrderedFourBlocks a r s := by
  have ha0 : 0 ≤ a := (le_max_left 0 (2 * r - s)).trans ha
  have hars : 2 * r - s ≤ a := (le_max_right 0 (2 * r - s)).trans ha
  exact ⟨ha0, by linarith, by linarith, by linarith⟩

theorem orderedFourBlocks_masses_sum {a r s : ℝ} :
    a + (r - a) + (s - r) + (1 - s) = 1 := by ring

/-- Average of the two exact outside-in logarithmic kernels. -/
def fourBlockMatching (z a r s : ℝ) : ℝ :=
  (logKernel (8 * z * a) (8 * z * (1 - s)) +
    logKernel (8 * z * (r - a)) (8 * z * (s - r))) / 2

theorem orderedFourBlocks_mass_nonneg {a r s : ℝ}
    (h : OrderedFourBlocks a r s) :
    0 ≤ a ∧ 0 ≤ r - a ∧ 0 ≤ s - r ∧ 0 ≤ 1 - s := by
  rcases h with ⟨ha0, h12, h23, h34⟩
  constructor
  · exact ha0
  constructor
  · exact ha0.trans h12
  constructor
  · exact (ha0.trans h12).trans h23
  · exact ((ha0.trans h12).trans h23).trans h34

end

end GDLowerBound.FourBlock
