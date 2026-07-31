import GDLowerBound.Matching.TotalWeight

/-!
# Finite labelled matchings

The endpoint map is injective on `Fin k × Bool`.  Thus every edge has two distinct endpoints,
different edges are vertex-disjoint, and labels remain distinct even when their numerical weights
coincide.  Ordering the edges and orienting each edge only gives a convenient finite encoding; the
edge kernel is symmetric, so these choices do not affect any extremal value.
-/

namespace GDLowerBound.Matching

open scoped BigOperators

noncomputable section

/-- A labelled matching with exactly `k` edges on the label type `α`. -/
structure LabeledMatching (α : Type*) (k : ℕ) where
  endpoints : (Fin k × Bool) ↪ α

namespace LabeledMatching

variable {α β : Type*} {k : ℕ}

@[ext]
theorem ext {M N : LabeledMatching α k} (h : M.endpoints = N.endpoints) : M = N := by
  cases M
  cases N
  cases h
  rfl

/-- The first endpoint of edge `i`. -/
def left (M : LabeledMatching α k) (i : Fin k) : α := M.endpoints (i, false)

/-- The second endpoint of edge `i`. -/
def right (M : LabeledMatching α k) (i : Fin k) : α := M.endpoints (i, true)

theorem left_injective (M : LabeledMatching α k) : Function.Injective M.left := by
  intro i j hij
  have hp : (i, false) = (j, false) := M.endpoints.injective hij
  exact congrArg Prod.fst hp

theorem right_injective (M : LabeledMatching α k) : Function.Injective M.right := by
  intro i j hij
  have hp : (i, true) = (j, true) := M.endpoints.injective hij
  exact congrArg Prod.fst hp

/-- No left endpoint can equal any right endpoint, including one from another edge. -/
theorem left_ne_right (M : LabeledMatching α k) (i j : Fin k) : M.left i ≠ M.right j := by
  intro hij
  have hp : (i, false) = (j, true) := M.endpoints.injective hij
  have := congrArg Prod.snd hp
  simp at this

/-- Relabel a matching along an equivalence of its label types. -/
def relabel (e : α ≃ β) (M : LabeledMatching α k) : LabeledMatching β k where
  endpoints := M.endpoints.trans e.toEmbedding

@[simp]
theorem left_relabel (e : α ≃ β) (M : LabeledMatching α k) (i : Fin k) :
    (M.relabel e).left i = e (M.left i) := by
  rfl

@[simp]
theorem right_relabel (e : α ≃ β) (M : LabeledMatching α k) (i : Fin k) :
    (M.relabel e).right i = e (M.right i) := by
  rfl

@[simp]
theorem relabel_symm_relabel (e : α ≃ β) (M : LabeledMatching α k) :
    (M.relabel e).relabel e.symm = M := by
  apply ext
  ext z
  simp [relabel]

end LabeledMatching

noncomputable instance labeledMatchingFinite [Finite α] (k : ℕ) :
    Finite (LabeledMatching α k) :=
  Finite.of_injective (fun M z ↦ M.endpoints z) (by
    intro M N h
    apply LabeledMatching.ext
    ext z
    exact congrFun h z)

noncomputable instance labeledMatchingFintype [Fintype α] (k : ℕ) :
    Fintype (LabeledMatching α k) := Fintype.ofFinite _

/-- The product of the `ψ`-weights of all edges in a labelled matching. -/
def matchingProduct {α : Type*} {k : ℕ} (w : α → ℝ) (M : LabeledMatching α k) : ℝ :=
  ∏ i, psi (w (M.left i)) (w (M.right i))

@[simp]
theorem matchingProduct_zero {α : Type*} (w : α → ℝ) (M : LabeledMatching α 0) :
    matchingProduct w M = 1 := by
  simp [matchingProduct]

@[simp]
theorem matchingProduct_relabel {α β : Type*} {k : ℕ} (e : α ≃ β) (w : α → ℝ)
    (M : LabeledMatching α k) :
    matchingProduct (fun b ↦ w (e.symm b)) (M.relabel e) = matchingProduct w M := by
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- The finite set of products attained by `k`-edge matchings. -/
def matchingValues [Fintype α] (w : α → ℝ) (k : ℕ) : Finset ℝ :=
  Finset.univ.image (fun M : LabeledMatching α k ↦ matchingProduct w M)

/-- The exact maximum matching product. It is `0` only when no `k`-edge matching exists. -/
noncomputable def Pψ [Fintype α] (w : α → ℝ) (k : ℕ) : ℝ :=
  if h : (matchingValues w k).Nonempty then (matchingValues w k).max' h else 0

theorem matchingValues_nonempty [Fintype α] (w : α → ℝ) {k : ℕ}
    (M : LabeledMatching α k) : (matchingValues w k).Nonempty := by
  exact ⟨matchingProduct w M, Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩⟩

theorem matchingValues_nonempty_iff [Fintype α] (w : α → ℝ) (k : ℕ) :
    (matchingValues w k).Nonempty ↔ Nonempty (LabeledMatching α k) := by
  constructor
  · rintro ⟨value, hvalue⟩
    rcases Finset.mem_image.mp hvalue with ⟨M, _, _⟩
    exact ⟨M⟩
  · rintro ⟨M⟩
    exact matchingValues_nonempty w M

/-- Every feasible matching product is bounded by the exact finite maximum. -/
theorem matchingProduct_le_Pψ [Fintype α] (w : α → ℝ) {k : ℕ}
    (M : LabeledMatching α k) : matchingProduct w M ≤ Pψ w k := by
  classical
  let hne := matchingValues_nonempty w M
  rw [Pψ, dif_pos hne]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩)

/-- On every feasible cardinality, the exact maximum is attained by a labelled matching. -/
theorem exists_matchingProduct_eq_Pψ [Fintype α] (w : α → ℝ) {k : ℕ}
    (hne : Nonempty (LabeledMatching α k)) :
    ∃ M : LabeledMatching α k, matchingProduct w M = Pψ w k := by
  classical
  let M₀ := Classical.choice hne
  let hs := matchingValues_nonempty w M₀
  rw [Pψ, dif_pos hs]
  have hmem := Finset.max'_mem (matchingValues w k) hs
  rcases Finset.mem_image.mp hmem with ⟨M, _, hM⟩
  exact ⟨M, hM⟩

/-- Feasibility is exactly the usual cardinality constraint `2k ≤ |α|`. -/
theorem labeledMatching_nonempty_iff [Fintype α] (k : ℕ) :
    Nonempty (LabeledMatching α k) ↔ 2 * k ≤ Fintype.card α := by
  constructor
  · rintro ⟨M⟩
    have hcard := Fintype.card_le_of_embedding M.endpoints
    simpa [Fintype.card_prod, Nat.mul_comm] using hcard
  · intro hcard
    have hemb : Nonempty ((Fin k × Bool) ↪ α) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa [Fintype.card_prod, Nat.mul_comm] using hcard
    exact hemb.map fun e ↦ ⟨e⟩

theorem exists_matchingProduct_eq_Pψ_of_card [Fintype α] (w : α → ℝ) {k : ℕ}
    (hcard : 2 * k ≤ Fintype.card α) :
    ∃ M : LabeledMatching α k, matchingProduct w M = Pψ w k :=
  exists_matchingProduct_eq_Pψ w ((labeledMatching_nonempty_iff k).2 hcard)

@[simp]
theorem Pψ_zero [Fintype α] (w : α → ℝ) : Pψ w 0 = 1 := by
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ_of_card w (k := 0) (by simp)
  simpa using hM.symm

theorem Pψ_eq_zero_of_infeasible [Fintype α] (w : α → ℝ) {k : ℕ}
    (hcard : Fintype.card α < 2 * k) : Pψ w k = 0 := by
  rw [Pψ, dif_neg]
  rwa [matchingValues_nonempty_iff, labeledMatching_nonempty_iff, not_le]

/-- Relabelling by an equivalence preserves the exact maximum. -/
theorem Pψ_relabel [Fintype α] [Fintype β] (e : α ≃ β) (w : α → ℝ) (k : ℕ) :
    Pψ (fun b ↦ w (e.symm b)) k = Pψ w k := by
  classical
  by_cases hne : Nonempty (LabeledMatching α k)
  · have hneβ : Nonempty (LabeledMatching β k) := hne.map (LabeledMatching.relabel e)
    obtain ⟨Mα, hMα⟩ := exists_matchingProduct_eq_Pψ w hne
    obtain ⟨Mβ, hMβ⟩ := exists_matchingProduct_eq_Pψ (fun b ↦ w (e.symm b)) hneβ
    apply le_antisymm
    · rw [← hMβ]
      have hle := matchingProduct_le_Pψ w (Mβ.relabel e.symm)
      calc
        matchingProduct (fun b ↦ w (e.symm b)) Mβ =
            matchingProduct w (Mβ.relabel e.symm) := by
          simpa using
            (matchingProduct_relabel e.symm (fun b ↦ w (e.symm b)) Mβ).symm
        _ ≤ Pψ w k := hle
    · rw [← hMα]
      have hle := matchingProduct_le_Pψ (fun b ↦ w (e.symm b)) (Mα.relabel e)
      calc
        matchingProduct w Mα =
            matchingProduct (fun b ↦ w (e.symm b)) (Mα.relabel e) := by
          exact (matchingProduct_relabel e w Mα).symm
        _ ≤ Pψ (fun b ↦ w (e.symm b)) k := hle
  · have hneβ : ¬ Nonempty (LabeledMatching β k) := by
      intro h
      exact hne (h.map (LabeledMatching.relabel e.symm))
    rw [Pψ, Pψ, dif_neg, dif_neg]
    · rwa [matchingValues_nonempty_iff]
    · rwa [matchingValues_nonempty_iff]

/-- The kernel is coordinatewise monotone on nonnegative weights. -/
theorem psi_mono_nonneg {u u' v v' : ℝ} (hu₀ : 0 ≤ u) (hv₀ : 0 ≤ v)
    (hu : u ≤ u') (hv : v ≤ v') : psi u v ≤ psi u' v' := by
  have hleft : psi u v ≤ psi u' v := by
    have hprod : 0 ≤ (u' - u) * (1 + v) :=
      mul_nonneg (sub_nonneg.mpr hu) (by linarith)
    simp only [psi]
    nlinarith
  have hu'₀ : 0 ≤ u' := hu₀.trans hu
  have hright : psi u' v ≤ psi u' v' := by
    have hprod : 0 ≤ (v' - v) * (1 + u') :=
      mul_nonneg (sub_nonneg.mpr hv) (by linarith)
    simp only [psi]
    nlinarith
  exact hleft.trans hright

theorem matchingProduct_nonneg {α : Type*} {k : ℕ} {w : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (M : LabeledMatching α k) : 0 ≤ matchingProduct w M := by
  exact Finset.prod_nonneg fun i _ ↦ psi_nonneg (hw (M.left i)) (hw (M.right i))

/-- Pointwise enlargement of nonnegative vertex weights enlarges every matching product. -/
theorem matchingProduct_mono {α : Type*} {k : ℕ} {w v : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hwv : ∀ a, w a ≤ v a) (M : LabeledMatching α k) :
    matchingProduct w M ≤ matchingProduct v M := by
  apply Finset.prod_le_prod
  · intro i _
    exact psi_nonneg (hw (M.left i)) (hw (M.right i))
  · intro i _
    exact psi_mono_nonneg (hw (M.left i)) (hw (M.right i))
      (hwv (M.left i)) (hwv (M.right i))

theorem Pψ_nonneg [Fintype α] {w : α → ℝ} {k : ℕ}
    (hw : ∀ a, 0 ≤ w a) (hne : Nonempty (LabeledMatching α k)) : 0 ≤ Pψ w k := by
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ w hne
  rw [← hM]
  exact matchingProduct_nonneg hw M

/-- Pointwise monotonicity of the exact matching maximum. -/
theorem Pψ_mono [Fintype α] {w v : α → ℝ} {k : ℕ}
    (hw : ∀ a, 0 ≤ w a) (hwv : ∀ a, w a ≤ v a)
    (hne : Nonempty (LabeledMatching α k)) : Pψ w k ≤ Pψ v k := by
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ w hne
  rw [← hM]
  exact (matchingProduct_mono hw hwv M).trans (matchingProduct_le_Pψ v M)

namespace LabeledMatching

/-- Include a labelled matching into a larger label type. -/
def map (e : α ↪ β) (M : LabeledMatching α k) : LabeledMatching β k where
  endpoints := M.endpoints.trans e

@[simp]
theorem left_map (e : α ↪ β) (M : LabeledMatching α k) (i : Fin k) :
    (M.map e).left i = e (M.left i) := rfl

@[simp]
theorem right_map (e : α ↪ β) (M : LabeledMatching α k) (i : Fin k) :
    (M.map e).right i = e (M.right i) := rfl

end LabeledMatching

/-- Adding labelled vertices cannot reduce the maximum when old weights are preserved. -/
theorem Pψ_le_of_embedding [Fintype α] [Fintype β] (e : α ↪ β)
    (w : α → ℝ) (v : β → ℝ) {k : ℕ}
    (hweight : ∀ a, v (e a) = w a) (hne : Nonempty (LabeledMatching α k)) :
    Pψ w k ≤ Pψ v k := by
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ w hne
  rw [← hM]
  calc
    matchingProduct w M = matchingProduct v (M.map e) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [hweight]
    _ ≤ Pψ v k := matchingProduct_le_Pψ v (M.map e)

/-- Uniform AM--GM, stated in the exact real-power form used for matching products. -/
theorem geomMean_le_arithMean_uniform {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ^ ((k : ℝ)⁻¹) ≤ (∑ i, z i) / k := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin k)) (fun _ ↦ (1 : ℝ)) z
    (fun _ _ ↦ by norm_num) (by simpa using hkℝ) (fun i _ ↦ hz i)
  simpa using hamgm

/-- A factorized pointwise bound for `ψ`; its slack is `(u-v)^2/8`. -/
theorem psi_le_sum_factor (u v : ℝ) :
    psi u v ≤ (u + v) * (u + v + 4) / 8 := by
  simp only [psi]
  nlinarith [sq_nonneg (u - v)]

/-- Pull a common `k`th real root through the factorized product. -/
theorem geomMean_sum_factor {k : ℕ} (hk : 0 < k) (s : Fin k → ℝ)
    (hs : ∀ i, 0 ≤ s i) :
    (∏ i, s i * (s i + 4) / 8) ^ ((k : ℝ)⁻¹) =
      (∏ i, s i) ^ ((k : ℝ)⁻¹) *
        (∏ i, (s i + 4)) ^ ((k : ℝ)⁻¹) / 8 := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hprod :
      (∏ i, s i * (s i + 4) / 8) =
        (∏ i, s i) * (∏ i, (s i + 4)) / (8 : ℝ) ^ k := by
    simp_rw [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp [Finset.prod_const, mul_assoc]
  rw [hprod]
  rw [Real.div_rpow (mul_nonneg (Finset.prod_nonneg fun i _ ↦ hs i)
      (Finset.prod_nonneg fun i _ ↦ by linarith [hs i])) (pow_nonneg (by norm_num) _)]
  rw [Real.mul_rpow (Finset.prod_nonneg fun i _ ↦ hs i)
      (Finset.prod_nonneg fun i _ ↦ by linarith [hs i])]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
  rw [mul_inv_cancel₀ hkℝ, Real.rpow_one]

/--
Total-weight bound for an arbitrary list of labelled, disjoint edge endpoints.  This direct
factorization is compatible with the outside-in estimate in `TotalWeight`: both have exactly the
same right-hand side, while this form avoids choosing a sorting permutation.
-/
theorem paired_geomMean_le_totalWeight {k : ℕ} (hk : 0 < k) (x y : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) ≤
      ((∑ i, x i) + ∑ i, y i) / (2 * k) +
        ((∑ i, x i) + ∑ i, y i) ^ 2 / (8 * (k : ℝ) ^ 2) := by
  let s : Fin k → ℝ := fun i ↦ x i + y i
  have hs : ∀ i, 0 ≤ s i := fun i ↦ add_nonneg (hx i) (hy i)
  have hpoint : ∀ i, psi (x i) (y i) ≤ s i * (s i + 4) / 8 := by
    intro i
    exact psi_le_sum_factor (x i) (y i)
  have hprod :
      (∏ i, psi (x i) (y i)) ≤ ∏ i, s i * (s i + 4) / 8 := by
    apply Finset.prod_le_prod
    · intro i _
      exact psi_nonneg (hx i) (hy i)
    · intro i _
      exact hpoint i
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hroot :
      (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) ≤
        (∏ i, s i * (s i + 4) / 8) ^ ((k : ℝ)⁻¹) := by
    exact Real.rpow_le_rpow
      (Finset.prod_nonneg fun i _ ↦ psi_nonneg (hx i) (hy i)) hprod (inv_nonneg.mpr hkℝ.le)
  have hgm₁ := geomMean_le_arithMean_uniform hk s hs
  have hgm₂ := geomMean_le_arithMean_uniform hk (fun i ↦ s i + 4) (fun i ↦ by linarith [hs i])
  have hmul :
      (∏ i, s i) ^ ((k : ℝ)⁻¹) * (∏ i, (s i + 4)) ^ ((k : ℝ)⁻¹) ≤
        ((∑ i, s i) / k) * ((∑ i, (s i + 4)) / k) := by
    exact mul_le_mul hgm₁ hgm₂
      (Real.rpow_nonneg (Finset.prod_nonneg fun i _ ↦ by linarith [hs i]) _)
      (div_nonneg (Finset.sum_nonneg fun i _ ↦ hs i) hkℝ.le)
  calc
    (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) ≤
        (∏ i, s i * (s i + 4) / 8) ^ ((k : ℝ)⁻¹) := hroot
    _ = (∏ i, s i) ^ ((k : ℝ)⁻¹) *
          (∏ i, (s i + 4)) ^ ((k : ℝ)⁻¹) / 8 :=
      geomMean_sum_factor hk s hs
    _ ≤ ((∑ i, s i) / k) * ((∑ i, (s i + 4)) / k) / 8 := by
      gcongr
    _ = ((∑ i, x i) + ∑ i, y i) / (2 * k) +
          ((∑ i, x i) + ∑ i, y i) ^ 2 / (8 * (k : ℝ) ^ 2) := by
      simp only [s, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fin]
      field_simp
      ring

/-- The total weight of the selected endpoints is at most the total weight of all labels. -/
theorem selectedWeight_le_total [Fintype α] {k : ℕ} (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (M : LabeledMatching α k) :
    (∑ i, w (M.left i)) + ∑ i, w (M.right i) ≤ ∑ a, w a := by
  classical
  have hsplit :
      (∑ i, w (M.left i)) + ∑ i, w (M.right i) =
        ∑ z : Fin k × Bool, w (M.endpoints z) := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [LabeledMatching.left, LabeledMatching.right, add_comm]
  rw [hsplit]
  calc
    (∑ z : Fin k × Bool, w (M.endpoints z)) =
        ∑ a ∈ (Finset.univ : Finset (Fin k × Bool)).map M.endpoints, w a := by
      rw [Finset.sum_map]
    _ ≤ ∑ a ∈ (Finset.univ : Finset α), w a := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ ↦ hw a)
    _ = ∑ a, w a := rfl

/-- The scalar right-hand side of the total-mass matching bound is monotone in total mass. -/
theorem totalWeightBound_mono {k : ℕ} (hk : 0 < k) {selected total : ℝ}
    (hselected₀ : 0 ≤ selected) (hst : selected ≤ total) :
    selected / (2 * k) + selected ^ 2 / (8 * (k : ℝ) ^ 2) ≤
      total / (2 * k) + total ^ 2 / (8 * (k : ℝ) ^ 2) := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have htotal₀ : 0 ≤ total := hselected₀.trans hst
  field_simp
  nlinarith

/-- Total-mass estimate for every concrete labelled matching. -/
theorem matchingProduct_geomMean_le_total [Fintype α] {k : ℕ} (hk : 0 < k)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (M : LabeledMatching α k) :
    (matchingProduct w M) ^ ((k : ℝ)⁻¹) ≤
      (∑ a, w a) / (2 * k) + (∑ a, w a) ^ 2 / (8 * (k : ℝ) ^ 2) := by
  let selected := (∑ i, w (M.left i)) + ∑ i, w (M.right i)
  have hselected₀ : 0 ≤ selected := by
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ hw (M.left i))
      (Finset.sum_nonneg fun i _ ↦ hw (M.right i))
  calc
    (matchingProduct w M) ^ ((k : ℝ)⁻¹) ≤
        selected / (2 * k) + selected ^ 2 / (8 * (k : ℝ) ^ 2) := by
      exact paired_geomMean_le_totalWeight hk
        (fun i ↦ w (M.left i)) (fun i ↦ w (M.right i))
        (fun i ↦ hw (M.left i)) (fun i ↦ hw (M.right i))
    _ ≤ (∑ a, w a) / (2 * k) + (∑ a, w a) ^ 2 / (8 * (k : ℝ) ^ 2) :=
      totalWeightBound_mono hk hselected₀ (selectedWeight_le_total w hw M)

/--
The manuscript's total-mass matching lemma for the exact labelled maximum `Pψ(W,k)`.
The cardinality assumption is equivalent to `k ≤ ⌊|W|/2⌋`.
-/
theorem Pψ_geomMean_le_total [Fintype α] {k : ℕ} (hk : 0 < k)
    (hcard : 2 * k ≤ Fintype.card α) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (Pψ w k) ^ ((k : ℝ)⁻¹) ≤
      (∑ a, w a) / (2 * k) + (∑ a, w a) ^ 2 / (8 * (k : ℝ) ^ 2) := by
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ_of_card w hcard
  rw [← hM]
  exact matchingProduct_geomMean_le_total hk w hw M

end

end GDLowerBound.Matching
