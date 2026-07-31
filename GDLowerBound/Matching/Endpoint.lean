import GDLowerBound.Matching.Labeled
import GDLowerBound.RankAnalysis.Budget
import GDLowerBound.Schedule.Functional
import GDLowerBound.Schedule.TopChain

/-!
# The chronological endpoint matching bound

This file formalizes the reduction from the local factors of the chronological top-rank chain to
two labelled matchings on an augmented path.  Path vertices are labelled by `Fin (q + 1)`; the last
label is the terminal auxiliary vertex.
-/

namespace GDLowerBound.Matching

open scoped BigOperators
open GDLowerBound.Schedule
open GDLowerBound.RankAnalysis

noncomputable section

/-- Number of zero-based even path edges among `q` edges. -/
def kPlus (q : ℕ) : ℕ := (q + 1) / 2

/-- Number of zero-based odd path edges among `q` edges. -/
def kMinus (q : ℕ) : ℕ := q / 2

theorem kPlus_add_kMinus (q : ℕ) : kPlus q + kMinus q = q := by
  simp only [kPlus, kMinus]
  omega

theorem two_kPlus_le (q : ℕ) : 2 * kPlus q ≤ q + 1 := by
  simp only [kPlus]
  omega

theorem two_kMinus_le (q : ℕ) : 2 * kMinus q ≤ q + 1 := by
  simp only [kMinus]
  omega

@[simp]
theorem kPlus_two : kPlus 2 = 1 := by decide

@[simp]
theorem kMinus_two : kMinus 2 = 1 := by decide

@[simp]
theorem kMinus_one : kMinus 1 = 0 := by decide

theorem kPlus_pos {q : ℕ} (hq : 0 < q) : 0 < kPlus q := by
  simp only [kPlus]
  omega

theorem kMinus_pos {q : ℕ} (hq : 2 ≤ q) : 0 < kMinus q := by
  simp only [kMinus]
  omega

/-- The matching formed by path edges `0,2,4,…`. -/
def evenEdgeMatching (q : ℕ) : LabeledMatching (Fin (q + 1)) (kPlus q) where
  endpoints :=
    { toFun := fun z ↦
        ⟨2 * z.1 + if z.2 then 1 else 0, by
          have hz := z.1.isLt
          simp only [kPlus] at hz
          split <;> omega⟩
      inj' := by
        rintro ⟨i, b⟩ ⟨j, c⟩ hij
        have hv := congrArg Fin.val hij
        cases b <;> cases c <;> simp at hv ⊢ <;> omega }

/-- The matching formed by path edges `1,3,5,…`. -/
def oddEdgeMatching (q : ℕ) : LabeledMatching (Fin (q + 1)) (kMinus q) where
  endpoints :=
    { toFun := fun z ↦
        ⟨2 * z.1 + if z.2 then 2 else 1, by
          have hz := z.1.isLt
          simp only [kMinus] at hz
          split <;> omega⟩
      inj' := by
        rintro ⟨i, b⟩ ⟨j, c⟩ hij
        have hv := congrArg Fin.val hij
        cases b <;> cases c <;> simp at hv ⊢ <;> omega }

@[simp]
theorem evenEdgeMatching_left_val (q : ℕ) (i : Fin (kPlus q)) :
    ((evenEdgeMatching q).left i).val = 2 * i := rfl

@[simp]
theorem evenEdgeMatching_right_val (q : ℕ) (i : Fin (kPlus q)) :
    ((evenEdgeMatching q).right i).val = 2 * i + 1 := rfl

@[simp]
theorem oddEdgeMatching_left_val (q : ℕ) (i : Fin (kMinus q)) :
    ((oddEdgeMatching q).left i).val = 2 * i + 1 := rfl

@[simp]
theorem oddEdgeMatching_right_val (q : ℕ) (i : Fin (kMinus q)) :
    ((oddEdgeMatching q).right i).val = 2 * i + 2 := rfl

/-- Product of all edges of the augmented path, split by edge parity. -/
def parityPathProduct {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  matchingProduct v (evenEdgeMatching q) * matchingProduct v (oddEdgeMatching q)

/-- The order-free product of the two exact matching maxima. -/
def matchingEnvelope {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  Pψ v (kPlus q) * Pψ v (kMinus q)

/-- The `q` edges of the augmented chronological path. -/
def chronologicalPathProduct {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  ∏ i : Fin q, psi (v i.castSucc) (v i.succ)

/-- Interleave the even and odd edge indices. -/
def edgeParityMap (q : ℕ) : Fin (kPlus q) ⊕ Fin (kMinus q) → Fin q
  | Sum.inl i => ⟨2 * i, by
      have hi := i.isLt
      simp only [kPlus] at hi
      omega⟩
  | Sum.inr i => ⟨2 * i + 1, by
      have hi := i.isLt
      simp only [kMinus] at hi
      omega⟩

theorem edgeParityMap_injective (q : ℕ) : Function.Injective (edgeParityMap q) := by
  rintro (i | i) (j | j) hij
  · have hv := congrArg Fin.val hij
    simp [edgeParityMap] at hv
    congr 1
    apply Fin.ext
    omega
  · have hv := congrArg Fin.val hij
    simp [edgeParityMap] at hv
    exfalso
    omega
  · have hv := congrArg Fin.val hij
    simp [edgeParityMap] at hv
    exfalso
    omega
  · have hv := congrArg Fin.val hij
    simp [edgeParityMap] at hv
    congr 1
    apply Fin.ext
    omega

/-- The parity interleaving is an equivalence because the two parity classes contain exactly `q`
edges altogether. -/
noncomputable def edgeParityEquiv (q : ℕ) :
    Fin (kPlus q) ⊕ Fin (kMinus q) ≃ Fin q :=
  Equiv.ofBijective (edgeParityMap q) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨edgeParityMap_injective q, by
      simp [kPlus_add_kMinus]⟩

@[simp]
theorem edgeParityEquiv_apply (q : ℕ) (i : Fin (kPlus q) ⊕ Fin (kMinus q)) :
    edgeParityEquiv q i = edgeParityMap q i := rfl

/-- Alternating path edges really do partition all path edges. -/
theorem parityPathProduct_eq_chronological {q : ℕ} (v : Fin (q + 1) → ℝ) :
    parityPathProduct v = chronologicalPathProduct v := by
  let f : Fin q → ℝ := fun i ↦ psi (v i.castSucc) (v i.succ)
  calc
    parityPathProduct v =
        ∏ z : Fin (kPlus q) ⊕ Fin (kMinus q), f (edgeParityEquiv q z) := by
      rw [Fintype.prod_sum_type]
      apply congrArg₂ (fun x y : ℝ ↦ x * y)
      · apply Finset.prod_congr rfl
        intro i _
        simp only [f, edgeParityEquiv_apply, edgeParityMap]
        apply congrArg₂ psi
        · apply congrArg v
          apply Fin.ext
          simp
        · apply congrArg v
          apply Fin.ext
          simp
      · apply Finset.prod_congr rfl
        intro i _
        simp only [f, edgeParityEquiv_apply, edgeParityMap]
        apply congrArg₂ psi
        · apply congrArg v
          apply Fin.ext
          simp
        · apply congrArg v
          apply Fin.ext
          simp
    _ = ∏ i : Fin q, f i := (edgeParityEquiv q).prod_comp f
    _ = chronologicalPathProduct v := rfl

/-- At the smallest admissible cutoff, the path has exactly one edge in each matching. -/
theorem parityPathProduct_two (v : Fin 3 → ℝ) :
    parityPathProduct v = psi (v 0) (v 1) * psi (v 1) (v 2) := by
  rw [parityPathProduct_eq_chronological]
  simp only [chronologicalPathProduct, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  apply congrArg₂ (fun x y : ℝ ↦ x * y)
  · apply congrArg₂ psi
    · apply congrArg v
      apply Fin.ext
      rfl
    · apply congrArg v
      apply Fin.ext
      rfl
  · apply congrArg₂ psi
    · apply congrArg v
      apply Fin.ext
      rfl
    · apply congrArg v
      apply Fin.ext
      rfl

/-- The algebraic normalization that turns the equalized local factors into the augmented path.
The final path vertex is auxiliary; `hn` is precisely the condition needed for its weight `1/n`. -/
theorem normalizedBudgetProduct_eq_path {n : ℕ} (hn : 0 < n) (D : ℝ)
    (ξ : Fin (n + 1) → ℝ) (v : Fin (n + 2) → ℝ)
    (hv : ∀ i : Fin (n + 1),
      v i.castSucc = 2 * D / (n + 1) * ξ i)
    (hvlast : v (Fin.last (n + 1)) = 1 / (n : ℝ)) :
    (1 + 2 * D * ξ (Fin.last n)) * (D / (n + 1)) ^ (n + 1) *
        ∏ i : Fin (n + 1),
          (Fin.lastCases 1
              (fun j : Fin n ↦ ξ j.castSucc + ξ j.succ) i +
            2 * (D / (n + 1)) *
              Fin.lastCases 0
                (fun j : Fin n ↦ ξ j.castSucc * ξ j.succ) i) =
      (2 * D * n / (n + 1)) * chronologicalPathProduct v := by
  let ubar : ℝ := D / (n + 1)
  let C : Fin n → ℝ := fun i ↦
    ξ i.castSucc + ξ i.succ + 2 * ubar * (ξ i.castSucc * ξ i.succ)
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqreal : (n + 1 : ℝ) ≠ 0 := by positivity
  have hedge (i : Fin n) :
      ubar * C i =
        psi (v i.castSucc.castSucc) (v i.castSucc.succ) := by
    rw [hv i.castSucc]
    have hidx : i.castSucc.succ = i.succ.castSucc := by
      apply Fin.ext
      simp
    rw [hidx, hv i.succ]
    dsimp only [ubar, C, psi]
    field_simp [hqreal]
  have hinter :
      ubar ^ n * ∏ i : Fin n, C i =
        ∏ i : Fin n, psi (v i.castSucc.castSucc) (v i.castSucc.succ) := by
    calc
      ubar ^ n * ∏ i : Fin n, C i =
          (∏ _i : Fin n, ubar) * ∏ i : Fin n, C i := by simp
      _ = ∏ i : Fin n, ubar * C i := Finset.prod_mul_distrib.symm
      _ = ∏ i : Fin n,
          psi (v i.castSucc.castSucc) (v i.castSucc.succ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hedge i
  have hterminal :
      ubar * (1 + 2 * D * ξ (Fin.last n)) =
        (2 * D * n / (n + 1)) *
          psi (v (Fin.last n).castSucc) (v (Fin.last n).succ) := by
    rw [hv (Fin.last n)]
    have haux : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    rw [haux, hvlast]
    dsimp only [ubar, psi]
    field_simp [hnreal, hqreal]
    ring
  have hcoeffProd :
      (∏ i : Fin (n + 1),
          (Fin.lastCases 1
              (fun j : Fin n ↦ ξ j.castSucc + ξ j.succ) i +
            2 * ubar *
              Fin.lastCases 0
                (fun j : Fin n ↦ ξ j.castSucc * ξ j.succ) i)) =
        ∏ i : Fin n, C i := by
    rw [Fin.prod_univ_castSucc]
    simp [C]
  change (1 + 2 * D * ξ (Fin.last n)) * ubar ^ (n + 1) * _ = _
  rw [hcoeffProd, pow_succ, chronologicalPathProduct, Fin.prod_univ_castSucc]
  calc
    (1 + 2 * D * ξ (Fin.last n)) * (ubar ^ n * ubar) * ∏ i, C i =
        (ubar * (1 + 2 * D * ξ (Fin.last n))) *
          (ubar ^ n * ∏ i, C i) := by ring
    _ = ((2 * D * n / (n + 1)) *
          psi (v (Fin.last n).castSucc) (v (Fin.last n).succ)) *
        (∏ i : Fin n, psi (v i.castSucc.castSucc) (v i.castSucc.succ)) := by
      rw [hterminal, hinter]
    _ = (2 * D * n / (n + 1)) *
        ((∏ i : Fin n, psi (v i.castSucc.castSucc) (v i.castSucc.succ)) *
          psi (v (Fin.last n).castSucc) (v (Fin.last n).succ)) := by ring

theorem parityPathProduct_le_matchingEnvelope {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) : parityPathProduct v ≤ matchingEnvelope v := by
  have heven₀ := matchingProduct_nonneg hv (evenEdgeMatching q)
  have hcard : 2 * kPlus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kPlus_le q
  have hmaxEven₀ := Pψ_nonneg hv ((labeledMatching_nonempty_iff (kPlus q)).2 hcard)
  exact mul_le_mul
    (matchingProduct_le_Pψ v (evenEdgeMatching q))
    (matchingProduct_le_Pψ v (oddEdgeMatching q))
    (matchingProduct_nonneg hv (oddEdgeMatching q)) hmaxEven₀

theorem parityPathProduct_pos {q : ℕ} {v : Fin (q + 1) → ℝ}
    (hv : ∀ i, 0 < v i) : 0 < parityPathProduct v := by
  have hedge {a b : Fin (q + 1)} : 0 < psi (v a) (v b) := by
    have ha := hv a
    have hb := hv b
    have hab : 0 < v a * v b := mul_pos ha hb
    unfold psi
    nlinarith
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    exact hedge
  · apply Finset.prod_pos
    intro i _
    exact hedge

/-- Chronological reciprocal weights plus the terminal auxiliary vertex. -/
def topPathWeight {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) : Fin (q + 1) → ℝ := fun j ↦
  if hj : j.val < q then
    2 * unresolvedMass h q /
      (q * excess h ((topChain h q).selected ⟨j, by
        simpa [topChain_length_of_le h hq] using hj⟩))
  else
    1 / (q - 1)

theorem topPathWeight_of_lt {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) (j : Fin (q + 1)) (hj : j.val < q) :
    topPathWeight h q hq j =
      2 * unresolvedMass h q /
        (q * excess h ((topChain h q).selected ⟨j, by
          simpa [topChain_length_of_le h hq] using hj⟩)) := by
  simp [topPathWeight, hj]

theorem topPathWeight_last {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    topPathWeight h q hq (Fin.last q) = 1 / (q - 1) := by
  simp [topPathWeight]

theorem topPathWeight_pos {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {q : ℕ} (hq₂ : 2 ≤ q) (hq : q ≤ longCount h) (j : Fin (q + 1)) :
    0 < topPathWeight h q hq j := by
  unfold topPathWeight
  split_ifs with hj
  · have hD := unresolvedMass_pos hh q
    have hc := (topChain h q).selected_excess_pos
      ⟨j, by simpa [topChain_length_of_le h hq] using hj⟩
    positivity
  · have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq₂
    have hreal : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    exact one_div_pos.mpr hreal

/-- Cast a chronological position into the (definitionally possibly shorter) top chain. -/
def topChainIndex {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) : Fin (topChain h q).length :=
  Fin.cast (topChain_length_of_le h hq).symm i

@[simp]
theorem topChainIndex_val {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) :
    (topChainIndex h q hq i).val = i.val := rfl

/-- Selected excesses in chronological rather than rank order. -/
def chronologicalExcess {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  excess h ((topChain h q).selected (topChainIndex h q hq i))

/-- Preceding gap masses for the chronological top chain. -/
def chronologicalPrecedingMass {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  (topChain h q).precedingMass (topChainIndex h q hq i)

/-- Local factors of the chronological top chain, indexed by `Fin q`. -/
def chronologicalLocalBound {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) : ℝ :=
  (topChain h q).localBound (topChainIndex h q hq i)

theorem chronologicalExcess_pos {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (hq : q ≤ longCount h) (i : Fin q) :
    0 < chronologicalExcess h q hq i :=
  (topChain h q).selected_excess_pos (topChainIndex h q hq i)

theorem chronologicalPrecedingMass_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (q : ℕ) (hq : q ≤ longCount h) (i : Fin q) :
    0 < chronologicalPrecedingMass h q hq i :=
  (topChain h q).precedingMass_pos hh (topChainIndex h q hq i)

theorem chronologicalLocalBound_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (q : ℕ) (hq : q ≤ longCount h) (i : Fin q) :
    0 < chronologicalLocalBound h q hq i :=
  (topChain h q).localBound_pos hh (topChainIndex h q hq i)

/-- Reindexing a top chain by its known length preserves its value product. -/
theorem topChain_value_eq_chronological {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq : q ≤ longCount h) :
    (topChain h q).value =
      (topChain h q).terminalScale⁻¹ *
        ∏ i : Fin q, chronologicalLocalBound h q hq i := by
  let e : Fin q ≃ Fin (topChain h q).length :=
    (Fin.castOrderIso (topChain_length_of_le h hq).symm).toEquiv
  unfold Chain.value
  congr 1
  rw [← e.prod_comp (fun i ↦ (topChain h q).localBound i)]
  apply Finset.prod_congr rfl
  intro i _
  rfl

/-- The internal augmented-path weights are scaled reciprocals of the chronological excesses. -/
theorem topPathWeight_castSucc {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq₀ : 0 < q) (hq : q ≤ longCount h) (i : Fin q) :
    topPathWeight h q hq i.castSucc =
      2 * unresolvedMass h q / q * (chronologicalExcess h q hq i)⁻¹ := by
  unfold topPathWeight
  split_ifs with hj
  swap
  · exfalso
    exact hj (by simp)
  let j : Fin (topChain h q).length :=
    ⟨i.castSucc.val, by
      simp [topChain_length_of_le h hq] at hj ⊢
      ⟩
  change 2 * unresolvedMass h q /
      (q * excess h ((topChain h q).selected j)) = _
  have hidx : j = topChainIndex h q hq i := by
    apply Fin.ext
    rfl
  rw [hidx]
  change 2 * unresolvedMass h q /
      (q * chronologicalExcess h q hq i) = _
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have hc := (chronologicalExcess_pos h q hq i).ne'
  field_simp [hqreal, hc]

/-- Reindexing by `Fin q` does not alter the sum of the initial gap masses. -/
theorem chronologicalPrecedingMass_sum_eq {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq : q ≤ longCount h) :
    (∑ i : Fin q, chronologicalPrecedingMass h q hq i) =
      ∑ i ∈ Finset.range q, (topChain h q).gapMass i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (topChain h q).gapMass i) q]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The top-chain preceding masses obey the unresolved-mass budget. -/
theorem chronologicalPrecedingMass_sum_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq : q ≤ longCount h) :
    ∑ i : Fin q, chronologicalPrecedingMass h q hq i ≤ unresolvedMass h q := by
  have hsum := topChain_initial_gap_sum_le hh hq
  have heq :
      (∑ i : Fin q, chronologicalPrecedingMass h q hq i) =
        ∑ i ∈ Finset.range q, (topChain h q).gapMass i :=
    chronologicalPrecedingMass_sum_eq h hq
  rw [heq]
  linarith

/-- The last preceding mass and terminal scale satisfy the terminal local-factor budget. -/
theorem chronologicalLastMass_add_terminal_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (n : ℕ)
    (hq : n + 1 ≤ longCount h) :
    chronologicalPrecedingMass h (n + 1) hq (Fin.last n) +
        (topChain h (n + 1)).terminalScale ≤
      2 * unresolvedMass h (n + 1) := by
  let u : Fin (n + 1) → ℝ :=
    chronologicalPrecedingMass h (n + 1) hq
  have hu (i : Fin (n + 1)) : 0 ≤ u i :=
    (chronologicalPrecedingMass_pos hh (n + 1) hq i).le
  have hlast : u (Fin.last n) ≤ ∑ i, u i := by
    exact Finset.single_le_sum (fun i _ ↦ hu i) (Finset.mem_univ (Fin.last n))
  have hmass := topChain_mass_decomposition h hq
  have hsumEq := chronologicalPrecedingMass_sum_eq h hq
  change (∑ i, u i) = _ at hsumEq
  rw [← hsumEq] at hmass
  have hterminal := topChain_terminalScale h hq
  have hsumNonneg : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ ↦ hu i
  change u (Fin.last n) + (topChain h (n + 1)).terminalScale ≤ _
  linarith

/-! ## Local reciprocal identities -/

/-- Expanding one local factor exposes the preceding mass, the selected excess, and the next
block scale.  This is the zero-based form of the first identity in
`eq:local-factor-identities`. -/
theorem localBound_inv_identity {T : ℕ} {h : StepSchedule T} (c : Chain h)
    (hh : IsNonnegativeSchedule h) (i : Fin c.length) :
    (c.localBound i)⁻¹ =
      c.precedingMass i / excess h (c.selected i) +
      c.precedingMass i / c.blockScale i.succ +
      c.precedingMass i ^ 2 /
        (excess h (c.selected i) * c.blockScale i.succ) := by
  have hy := c.selected_excess_pos i
  have hU := c.precedingMass_pos hh i
  have hH := c.blockScale_pos hh i.succ
  rw [Chain.localBound, Chain.blockScale_castSucc]
  unfold Chain.nonterminalScale
  field_simp [hy.ne', hU.ne', hH.ne']
  ring

/-- The exact terminal reciprocal identity for a nonempty chronological chain. -/
theorem terminal_localBound_inv_identity {T : ℕ} {h : StepSchedule T}
    (c : Chain h) (hh : IsNonnegativeSchedule h) (n : ℕ)
    (hlen : c.length = n + 1) :
    c.terminalScale * (c.localBound (Fin.cast hlen.symm (Fin.last n)))⁻¹ =
      c.precedingMass (Fin.cast hlen.symm (Fin.last n)) *
        (1 +
          (c.precedingMass (Fin.cast hlen.symm (Fin.last n)) + c.terminalScale) /
            excess h (c.selected (Fin.cast hlen.symm (Fin.last n)))) := by
  let i : Fin c.length := Fin.cast hlen.symm (Fin.last n)
  have hi_last : i.succ = Fin.last c.length := by
    apply Fin.ext
    simp [i, hlen]
  have hy := c.selected_excess_pos i
  have hU := c.precedingMass_pos hh i
  have hH := c.terminalScale_pos hh
  change c.terminalScale * (c.localBound i)⁻¹ =
    c.precedingMass i *
      (1 + (c.precedingMass i + c.terminalScale) / excess h (c.selected i))
  rw [Chain.localBound, Chain.blockScale_castSucc, hi_last, Chain.blockScale_last]
  unfold Chain.nonterminalScale
  field_simp [hy.ne', hU.ne', hH.ne']
  ring

/-- A nonterminal reciprocal is bounded by a quadratic expression involving only two consecutive
selected excesses and the preceding gap mass. -/
theorem localBound_inv_le_next {T : ℕ} {h : StepSchedule T} (c : Chain h)
    (hh : IsNonnegativeSchedule h) (i : Fin c.length)
    (hi : i.val + 1 < c.length) :
    (c.localBound i)⁻¹ ≤
      c.precedingMass i *
        ((excess h (c.selected i))⁻¹ +
          (excess h (c.selected ⟨i.val + 1, hi⟩))⁻¹) +
      c.precedingMass i ^ 2 *
        ((excess h (c.selected i))⁻¹ *
          (excess h (c.selected ⟨i.val + 1, hi⟩))⁻¹) := by
  let j : Fin c.length := ⟨i.val + 1, hi⟩
  have hy := c.selected_excess_pos i
  have hz := c.selected_excess_pos j
  have hU := c.precedingMass_pos hh i
  have hnext : c.blockScale i.succ = c.nonterminalScale j := by
    simp [Chain.blockScale, hi, j]
  have hscale : excess h (c.selected j) ≤ c.blockScale i.succ := by
    rw [hnext]
    unfold Chain.nonterminalScale
    have := c.precedingMass_pos hh j
    linarith
  have hH := c.blockScale_pos hh i.succ
  have hlinear :
      c.precedingMass i / c.blockScale i.succ ≤
        c.precedingMass i / excess h (c.selected j) :=
    div_le_div_of_nonneg_left hU.le hz hscale
  have hden :
      excess h (c.selected i) * excess h (c.selected j) ≤
        excess h (c.selected i) * c.blockScale i.succ := by
    exact mul_le_mul_of_nonneg_left hscale hy.le
  have hquad :
      c.precedingMass i ^ 2 /
          (excess h (c.selected i) * c.blockScale i.succ) ≤
        c.precedingMass i ^ 2 /
          (excess h (c.selected i) * excess h (c.selected j)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hy hz) hden
  rw [localBound_inv_identity c hh i]
  change _ ≤ c.precedingMass i * (_ + _) + c.precedingMass i ^ 2 * (_ * _)
  simp only [inv_eq_one_div]
  have hresult :
      c.precedingMass i / excess h (c.selected i) +
          c.precedingMass i / c.blockScale i.succ +
          c.precedingMass i ^ 2 /
            (excess h (c.selected i) * c.blockScale i.succ) ≤
        c.precedingMass i *
          (1 / excess h (c.selected i) + 1 / excess h (c.selected j)) +
        c.precedingMass i ^ 2 *
          (1 / excess h (c.selected i) * 1 / excess h (c.selected j)) := by
    calc
    c.precedingMass i / excess h (c.selected i) +
          c.precedingMass i / c.blockScale i.succ +
          c.precedingMass i ^ 2 /
            (excess h (c.selected i) * c.blockScale i.succ) ≤
        c.precedingMass i / excess h (c.selected i) +
          c.precedingMass i / excess h (c.selected j) +
          c.precedingMass i ^ 2 /
            (excess h (c.selected i) * excess h (c.selected j)) := by
      gcongr
    _ = c.precedingMass i *
          (1 / excess h (c.selected i) + 1 / excess h (c.selected j)) +
        c.precedingMass i ^ 2 *
          (1 / excess h (c.selected i) * 1 / excess h (c.selected j)) := by
      field_simp [hy.ne', hz.ne']
  dsimp only [j] at hresult
  convert hresult using 1
  ring

/-- If the last preceding mass plus the terminal scale is at most `2D`, the terminal reciprocal
has the required one-variable bound. -/
theorem terminal_localBound_inv_le {T : ℕ} {h : StepSchedule T}
    (c : Chain h) (hh : IsNonnegativeSchedule h) (n : ℕ)
    (hlen : c.length = n + 1) {D : ℝ}
    (hmass : c.precedingMass (Fin.cast hlen.symm (Fin.last n)) +
        c.terminalScale ≤ 2 * D) :
    c.terminalScale * (c.localBound (Fin.cast hlen.symm (Fin.last n)))⁻¹ ≤
      c.precedingMass (Fin.cast hlen.symm (Fin.last n)) *
        (1 + 2 * D *
          (excess h (c.selected (Fin.cast hlen.symm (Fin.last n))))⁻¹) := by
  let i : Fin c.length := Fin.cast hlen.symm (Fin.last n)
  have hy := c.selected_excess_pos i
  have hU := c.precedingMass_pos hh i
  have hfrac :
      (c.precedingMass i + c.terminalScale) / excess h (c.selected i) ≤
        (2 * D) / excess h (c.selected i) :=
    div_le_div_of_nonneg_right (by simpa [i] using hmass) hy.le
  rw [terminal_localBound_inv_identity c hh n hlen]
  change c.precedingMass i * (1 + (c.precedingMass i + c.terminalScale) /
      excess h (c.selected i)) ≤
    c.precedingMass i *
      (1 + 2 * D * (excess h (c.selected i))⁻¹)
  calc
    c.precedingMass i *
        (1 + (c.precedingMass i + c.terminalScale) / excess h (c.selected i)) ≤
      c.precedingMass i * (1 + (2 * D) / excess h (c.selected i)) := by
        gcongr
    _ = c.precedingMass i *
        (1 + 2 * D * (excess h (c.selected i))⁻¹) := by
      rw [div_eq_mul_inv]

/-! ## The endpoint product bound -/

/-- The full reciprocal product of the chronological top chain is controlled by its augmented
path.  This is the factorized heart of Proposition `prop:endpoint-matching`. -/
theorem topChain_reciprocalProduct_le_path {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    (topChain h q).terminalScale *
        ∏ i : Fin q, (chronologicalLocalBound h q hq i)⁻¹ ≤
      (2 * unresolvedMass h q * (q - 1) / q) *
        parityPathProduct (topPathWeight h q hq) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  simp only [Nat.succ_eq_add_one] at hq₂ hq ⊢
  have hn : 0 < n := by omega
  let c : Chain h := topChain h (n + 1)
  let D : ℝ := unresolvedMass h (n + 1)
  let e : Fin (n + 1) → Fin c.length :=
    topChainIndex h (n + 1) hq
  let u : Fin (n + 1) → ℝ :=
    chronologicalPrecedingMass h (n + 1) hq
  let ξ : Fin (n + 1) → ℝ := fun i ↦
    (chronologicalExcess h (n + 1) hq i)⁻¹
  let χ : Fin (n + 1) → ℝ :=
    chronologicalLocalBound h (n + 1) hq
  let A : Fin (n + 1) → ℝ :=
    Fin.lastCases 1 (fun i : Fin n ↦ ξ i.castSucc + ξ i.succ)
  let B : Fin (n + 1) → ℝ :=
    Fin.lastCases 0 (fun i : Fin n ↦ ξ i.castSucc * ξ i.succ)
  have hlen : c.length = n + 1 := topChain_length_of_le h hq
  have hD : 0 < D := unresolvedMass_pos hh (n + 1)
  have hu (i : Fin (n + 1)) : 0 ≤ u i :=
    (chronologicalPrecedingMass_pos hh (n + 1) hq i).le
  have hξ (i : Fin (n + 1)) : 0 < ξ i := by
    exact inv_pos.mpr (chronologicalExcess_pos h (n + 1) hq i)
  have hA (i : Fin (n + 1)) : 0 ≤ A i := by
    refine Fin.lastCases (by simp [A]) (fun j ↦ ?_) i
    simp only [A, Fin.lastCases_castSucc]
    exact add_nonneg (hξ j.castSucc).le (hξ j.succ).le
  have hB (i : Fin (n + 1)) : 0 ≤ B i := by
    refine Fin.lastCases (by simp [B]) (fun j ↦ ?_) i
    simp only [B, Fin.lastCases_castSucc]
    exact mul_nonneg (hξ j.castSucc).le (hξ j.succ).le
  have hmass : ∑ i, u i ≤ D := by
    exact chronologicalPrecedingMass_sum_le hh hq
  have hinternal (i : Fin n) :
      (χ i.castSucc)⁻¹ ≤
        u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc) := by
    have hi : (e i.castSucc).val + 1 < c.length := by
      change i.val + 1 < c.length
      rw [topChain_length_of_le h hq]
      omega
    have hnext :
        (⟨(e i.castSucc).val + 1, hi⟩ : Fin c.length) = e i.succ := by
      apply Fin.ext
      simp [e]
    have hlocal := localBound_inv_le_next c hh (e i.castSucc) hi
    rw [hnext] at hlocal
    have hlocal' :
        (χ i.castSucc)⁻¹ ≤
          u i.castSucc * (ξ i.castSucc + ξ i.succ) +
            u i.castSucc ^ 2 * (ξ i.castSucc * ξ i.succ) := by
      simpa only [c, e, u, ξ, χ, chronologicalLocalBound,
        chronologicalPrecedingMass, chronologicalExcess] using hlocal
    calc
      (χ i.castSucc)⁻¹ ≤
          u i.castSucc * (ξ i.castSucc + ξ i.succ) +
            u i.castSucc ^ 2 * (ξ i.castSucc * ξ i.succ) := hlocal'
      _ = u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc) := by
        simp only [A, B, Fin.lastCases_castSucc]
        ring
  have hterminal :
      c.terminalScale * (χ (Fin.last n))⁻¹ ≤
        u (Fin.last n) * (1 + 2 * D * ξ (Fin.last n)) := by
    have hterminalMass := chronologicalLastMass_add_terminal_le hh n hq
    have hlocal := terminal_localBound_inv_le c hh n hlen
      (D := D) (by simpa only [c, e, u, D, topChainIndex,
        chronologicalPrecedingMass] using hterminalMass)
    simpa only [c, e, u, ξ, χ, chronologicalLocalBound,
      chronologicalPrecedingMass, chronologicalExcess, topChainIndex] using hlocal
  have hprodInternal :
      (∏ i : Fin n, (χ i.castSucc)⁻¹) ≤
        ∏ i : Fin n,
          u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc) := by
    apply Finset.prod_le_prod
    · intro i _
      exact (inv_pos.mpr (chronologicalLocalBound_pos hh (n + 1) hq i.castSucc)).le
    · intro i _
      exact hinternal i
  have hupperInternal :
      0 ≤ ∏ i : Fin n,
        u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc) := by
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (hu i.castSucc)
      (add_nonneg (hA i.castSucc) (mul_nonneg (hB i.castSucc) (hu i.castSucc)))
  have hterminalNonneg : 0 ≤ c.terminalScale * (χ (Fin.last n))⁻¹ := by
    exact mul_nonneg (c.terminalScale_pos hh).le
      (inv_nonneg.mpr (chronologicalLocalBound_pos hh (n + 1) hq (Fin.last n)).le)
  have hmultiplied :
      (∏ i : Fin n, (χ i.castSucc)⁻¹) *
          (c.terminalScale * (χ (Fin.last n))⁻¹) ≤
        (∏ i : Fin n,
            u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc)) *
          (u (Fin.last n) * (1 + 2 * D * ξ (Fin.last n))) :=
    mul_le_mul hprodInternal hterminal hterminalNonneg hupperInternal
  have hlocalProduct :
      c.terminalScale * ∏ i : Fin (n + 1), (χ i)⁻¹ ≤
        (1 + 2 * D * ξ (Fin.last n)) *
          (∏ i : Fin (n + 1), u i) *
          ∏ i : Fin (n + 1), (A i + B i * u i) := by
    calc
      c.terminalScale * ∏ i : Fin (n + 1), (χ i)⁻¹ =
          (∏ i : Fin n, (χ i.castSucc)⁻¹) *
            (c.terminalScale * (χ (Fin.last n))⁻¹) := by
        rw [Fin.prod_univ_castSucc]
        ring
      _ ≤ (∏ i : Fin n,
            u i.castSucc * (A i.castSucc + B i.castSucc * u i.castSucc)) *
          (u (Fin.last n) * (1 + 2 * D * ξ (Fin.last n))) := hmultiplied
      _ = (1 + 2 * D * ξ (Fin.last n)) *
          (∏ i : Fin (n + 1), u i) *
          ∏ i : Fin (n + 1), (A i + B i * u i) := by
        rw [Fin.prod_univ_castSucc (fun i ↦ u i),
          Fin.prod_univ_castSucc (fun i ↦ A i + B i * u i)]
        simp only [A, B, Fin.lastCases_last, zero_mul, add_zero]
        rw [Finset.prod_mul_distrib]
        ring
  have hbudget := budgetEqualization (q := n + 1) (by omega) hD u A B hu hA hB hmass
  have hterminalFactorNonneg : 0 ≤ 1 + 2 * D * ξ (Fin.last n) := by
    have hprod : 0 < D * ξ (Fin.last n) := mul_pos hD (hξ (Fin.last n))
    nlinarith
  have hequalized :
      (1 + 2 * D * ξ (Fin.last n)) *
          ((∏ i : Fin (n + 1), u i) *
            ∏ i : Fin (n + 1), (A i + B i * u i)) ≤
        (1 + 2 * D * ξ (Fin.last n)) *
          ((D / (n + 1)) ^ (n + 1) *
            ∏ i : Fin (n + 1), (A i + 2 * (D / (n + 1)) * B i)) :=
    mul_le_mul_of_nonneg_left
      (by simpa only [Nat.cast_add, Nat.cast_one] using hbudget)
      hterminalFactorNonneg
  have hv (i : Fin (n + 1)) :
      topPathWeight h (n + 1) hq i.castSucc =
        2 * D / (n + 1) * ξ i := by
    simpa only [D, ξ, Nat.cast_add, Nat.cast_one] using
      (topPathWeight_castSucc h (by omega) hq i)
  have hvlast :
      topPathWeight h (n + 1) hq (Fin.last (n + 1)) = 1 / (n : ℝ) := by
    simpa using topPathWeight_last h hq
  have hnormalize := normalizedBudgetProduct_eq_path hn D ξ
    (topPathWeight h (n + 1) hq) hv hvlast
  change c.terminalScale * ∏ i : Fin (n + 1), (χ i)⁻¹ ≤ _
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  calc
    c.terminalScale * ∏ i : Fin (n + 1), (χ i)⁻¹ ≤
        (1 + 2 * D * ξ (Fin.last n)) *
          ((∏ i : Fin (n + 1), u i) *
            ∏ i : Fin (n + 1), (A i + B i * u i)) := by
      simpa only [mul_assoc] using hlocalProduct
    _ ≤ (1 + 2 * D * ξ (Fin.last n)) *
          ((D / (n + 1)) ^ (n + 1) *
            ∏ i : Fin (n + 1), (A i + 2 * (D / (n + 1)) * B i)) := hequalized
    _ = (2 * D * n / (n + 1)) *
          chronologicalPathProduct (topPathWeight h (n + 1) hq) := by
      simpa only [A, B, mul_assoc] using hnormalize
    _ = (2 * unresolvedMass h (n + 1) * ((n + 1 : ℝ) - 1) /
          (n + 1 : ℝ)) * parityPathProduct (topPathWeight h (n + 1) hq) := by
      rw [parityPathProduct_eq_chronological]
      dsimp only [D]
      congr 2
      ring

/-- The chronological top chain has at least the order-independent matching contribution. -/
theorem topChain_value_ge_matchingEnvelope {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    (q : ℝ) /
        (2 * unresolvedMass h q * ((q : ℝ) - 1) *
          matchingEnvelope (topPathWeight h q hq)) ≤
      (topChain h q).value := by
  let c : Chain h := topChain h q
  let D : ℝ := unresolvedMass h q
  let v : Fin (q + 1) → ℝ := topPathWeight h q hq
  let M : ℝ := matchingEnvelope v
  let coeff : ℝ := 2 * D * ((q : ℝ) - 1) / q
  let R : ℝ := c.terminalScale *
    ∏ i : Fin q, (chronologicalLocalBound h q hq i)⁻¹
  let K : ℝ := coeff * M
  have hD : 0 < D := unresolvedMass_pos hh q
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq₂)
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq₂
    linarith
  have hvpos : ∀ i, 0 < v i := fun i ↦ topPathWeight_pos hh hq₂ hq i
  have hpathPos : 0 < parityPathProduct v := parityPathProduct_pos hvpos
  have hpathLe : parityPathProduct v ≤ M :=
    parityPathProduct_le_matchingEnvelope v (fun i ↦ (hvpos i).le)
  have hM : 0 < M := hpathPos.trans_le hpathLe
  have hcoeff : 0 < coeff := by
    dsimp only [coeff]
    positivity
  have hK : 0 < K := mul_pos hcoeff hM
  have hR : 0 < R := by
    dsimp only [R, c]
    apply mul_pos ((topChain h q).terminalScale_pos hh)
    apply Finset.prod_pos
    intro i _
    exact inv_pos.mpr (chronologicalLocalBound_pos hh q hq i)
  have hreciprocal : R ≤ coeff * parityPathProduct v := by
    simpa only [R, c, coeff, D, v] using
      (topChain_reciprocalProduct_le_path hh hq₂ hq)
  have hRK : R ≤ K := hreciprocal.trans <|
    mul_le_mul_of_nonneg_left hpathLe hcoeff.le
  have hinv : K⁻¹ ≤ R⁻¹ := (inv_le_inv₀ hK hR).2 hRK
  have hvalue : c.value = R⁻¹ := by
    rw [topChain_value_eq_chronological h hq]
    dsimp only [R, c]
    rw [mul_inv_rev, Finset.prod_inv_distrib]
    simp only [inv_inv]
    ring
  have hscalar :
      (q : ℝ) / (2 * D * ((q : ℝ) - 1) * M) = K⁻¹ := by
    dsimp only [K, coeff]
    field_simp [hD.ne', hqreal.ne', hqm1.ne', hM.ne']
  change (q : ℝ) / (2 * D * ((q : ℝ) - 1) * M) ≤ c.value
  rw [hscalar, hvalue]
  exact hinv

/-- **Order-independent endpoint matching bound.**  The maximum defining the schedule functional
contains the chronological chain of the top `q` excesses, so its contribution gives the advertised
lower bound.  This is Proposition `prop:endpoint-matching`. -/
theorem endpoint_matching_bound {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    (q : ℝ) /
        (2 * unresolvedMass h q * ((q : ℝ) - 1) *
          matchingEnvelope (topPathWeight h q hq)) ≤
      lowerBoundFunctional h := by
  exact (topChain_value_ge_matchingEnvelope hh hq₂ hq).trans
    (chainValue_le_functional h (topChain h q))

end

end GDLowerBound.Matching
