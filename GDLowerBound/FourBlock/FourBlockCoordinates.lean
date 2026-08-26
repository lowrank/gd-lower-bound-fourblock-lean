import GDLowerBound.FourBlock.FourBlockJensen

/-!
# Exact normalized coordinates for four sorted blocks

For `4m` positive weights, the definitions below turn the four quarter sums
into the manuscript coordinates `(z,a,r,s)`.  The normalization is chosen so
that the quarter means are exactly
`8*z*(a, r-a, s-r, 1-s)`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

def quarterSumOne {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  ∑ i, outsideQuarterOne w i

def quarterSumTwo {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  ∑ i, outsideQuarterTwo w i

def quarterSumThree {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  ∑ i, outsideQuarterThree w i

def quarterSumFour {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  ∑ i, outsideQuarterFour w i

def fourBlockTotal {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  quarterSumOne w + quarterSumTwo w + quarterSumThree w + quarterSumFour w

def fourBlockZ {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  fourBlockTotal w / (8 * m)

def fourBlockA {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  quarterSumOne w / fourBlockTotal w

def fourBlockR {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  (quarterSumOne w + quarterSumTwo w) / fourBlockTotal w

def fourBlockS {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : ℝ :=
  (quarterSumOne w + quarterSumTwo w + quarterSumThree w) / fourBlockTotal w

theorem quarterSum_pos {m : ℕ} (hm : 0 < m)
    (u : Fin m → ℝ) (hu : ∀ i, 0 < u i) : 0 < ∑ i, u i := by
  apply Finset.sum_pos
  · intro i hi
    exact hu i
  · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩

theorem fourBlockTotal_pos {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hw : ∀ i, 0 < w i) :
    0 < fourBlockTotal w := by
  have h1 := quarterSum_pos hm (outsideQuarterOne w) (fun i ↦ hw _)
  have h2 := quarterSum_pos hm (outsideQuarterTwo w) (fun i ↦ hw _)
  have h3 := quarterSum_pos hm (outsideQuarterThree w) (fun i ↦ hw _)
  have h4 := quarterSum_pos hm (outsideQuarterFour w) (fun i ↦ hw _)
  unfold fourBlockTotal quarterSumOne quarterSumTwo quarterSumThree quarterSumFour
  positivity

theorem finMean_outsideQuarterOne_eq {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hw : ∀ i, 0 < w i) :
    finMean (outsideQuarterOne w) = 8 * fourBlockZ w * fourBlockA w := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htotal := fourBlockTotal_pos hm hw
  unfold finMean fourBlockZ fourBlockA quarterSumOne
  field_simp [hmR.ne', htotal.ne']

theorem finMean_outsideQuarterTwo_eq {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hw : ∀ i, 0 < w i) :
    finMean (outsideQuarterTwo w) =
      8 * fourBlockZ w * (fourBlockR w - fourBlockA w) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htotal := fourBlockTotal_pos hm hw
  unfold finMean fourBlockZ fourBlockR fourBlockA quarterSumTwo
  field_simp [hmR.ne', htotal.ne']
  ring

theorem finMean_outsideQuarterThree_eq {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hw : ∀ i, 0 < w i) :
    finMean (outsideQuarterThree w) =
      8 * fourBlockZ w * (fourBlockS w - fourBlockR w) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htotal := fourBlockTotal_pos hm hw
  unfold finMean fourBlockZ fourBlockS fourBlockR quarterSumThree
  field_simp [hmR.ne', htotal.ne']
  ring

theorem finMean_outsideQuarterFour_eq {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hw : ∀ i, 0 < w i) :
    finMean (outsideQuarterFour w) =
      8 * fourBlockZ w * (1 - fourBlockS w) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htotal := fourBlockTotal_pos hm hw
  unfold finMean fourBlockZ fourBlockS
  field_simp [hmR.ne', htotal.ne']
  unfold fourBlockTotal quarterSumOne quarterSumTwo quarterSumThree quarterSumFour
  ring

/-- Exact finite form of the manuscript's four-block matching inequality. -/
theorem outsideInLogScore_average_le_fourBlockMatching {m : ℕ} (hm : 0 < m)
    (w : Fin (2 * (m + m)) → ℝ) (hw : ∀ i, 0 < w i) :
    outsideInLogScore (m + m) w / (2 * m) ≤
      fourBlockMatching (fourBlockZ w) (fourBlockA w)
        (fourBlockR w) (fourBlockS w) := by
  calc
    outsideInLogScore (m + m) w / (2 * m) ≤
        (logKernel (finMean (outsideQuarterOne w))
            (finMean (outsideQuarterFour w)) +
          logKernel (finMean (outsideQuarterTwo w))
            (finMean (outsideQuarterThree w))) / 2 :=
      outsideInLogScore_average_le_fourBlock hm w hw
    _ = fourBlockMatching (fourBlockZ w) (fourBlockA w)
          (fourBlockR w) (fourBlockS w) := by
      rw [finMean_outsideQuarterOne_eq hm hw,
        finMean_outsideQuarterTwo_eq hm hw,
        finMean_outsideQuarterThree_eq hm hw,
        finMean_outsideQuarterFour_eq hm hw]
      rfl

theorem quarterSumOne_le_two {m : ℕ} {w : Fin (2 * (m + m)) → ℝ}
    (hw : Monotone w) : quarterSumOne w ≤ quarterSumTwo w := by
  apply Finset.sum_le_sum
  intro i hi
  apply hw
  change i.val ≤ m + i.val
  omega

theorem quarterSumTwo_le_three {m : ℕ} {w : Fin (2 * (m + m)) → ℝ}
    (hw : Monotone w) : quarterSumTwo w ≤ quarterSumThree w := by
  apply Finset.sum_le_sum
  intro i hi
  apply hw
  change m + i.val ≤ 2 * (m + m) - 1 - (m + i.val)
  omega

theorem quarterSumThree_le_four {m : ℕ} {w : Fin (2 * (m + m)) → ℝ}
    (hw : Monotone w) : quarterSumThree w ≤ quarterSumFour w := by
  apply Finset.sum_le_sum
  intro i hi
  apply hw
  change 2 * (m + m) - 1 - (m + i.val) ≤ 2 * (m + m) - 1 - i.val
  omega

/-- Sorted positive weights give exactly the ordered four-block domain used by
the analytic and interval certificates. -/
theorem orderedFourBlocks_of_sortedWeights {m : ℕ} (hm : 0 < m)
    {w : Fin (2 * (m + m)) → ℝ} (hpos : ∀ i, 0 < w i)
    (hmono : Monotone w) :
    OrderedFourBlocks (fourBlockA w) (fourBlockR w) (fourBlockS w) := by
  have htotal := fourBlockTotal_pos hm hpos
  have h1pos : 0 ≤ quarterSumOne w :=
    (quarterSum_pos hm (outsideQuarterOne w) (fun i ↦ hpos _)).le
  have h12 := quarterSumOne_le_two hmono
  have h23 := quarterSumTwo_le_three hmono
  have h34 := quarterSumThree_le_four hmono
  have h2id : fourBlockR w - fourBlockA w =
      quarterSumTwo w / fourBlockTotal w := by
    unfold fourBlockR fourBlockA
    field_simp [htotal.ne']
    ring
  have h3id : fourBlockS w - fourBlockR w =
      quarterSumThree w / fourBlockTotal w := by
    unfold fourBlockS fourBlockR
    field_simp [htotal.ne']
    ring
  have h4id : 1 - fourBlockS w =
      quarterSumFour w / fourBlockTotal w := by
    unfold fourBlockS
    rw [one_sub_div htotal.ne']
    unfold fourBlockTotal
    ring
  unfold OrderedFourBlocks
  constructor
  · change 0 ≤ quarterSumOne w / fourBlockTotal w
    exact div_nonneg h1pos htotal.le
  constructor
  · rw [h2id]
    change quarterSumOne w / fourBlockTotal w ≤
      quarterSumTwo w / fourBlockTotal w
    exact div_le_div_of_nonneg_right h12 htotal.le
  constructor
  · rw [h2id, h3id]
    exact div_le_div_of_nonneg_right h23 htotal.le
  · rw [h3id, h4id]
    exact div_le_div_of_nonneg_right h34 htotal.le

end

end GDLowerBound.FourBlock
