import GDLowerBound.FourBlock.OutsideInTheorem

/-!
# Outside-in order for a matching with one unused vertex

For `2*k+1` sorted positive weights, a `k`-edge matching uses all but one
vertex.  Replacing a used least vertex by the unused vertex can only increase
the exact kernel product, so an optimizer may leave the least vertex unused.
The remaining matching is perfect and is covered by the preceding theorem.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Matching

noncomputable section

def tailWeight {k : ℕ} (w : Fin (2 * k + 1) → ℝ) : Fin (2 * k) → ℝ :=
  fun i ↦ w ⟨i + 1, by omega⟩

theorem tailWeight_pos {k : ℕ} {w : Fin (2 * k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) : ∀ i, 0 < tailWeight w i := by
  intro i
  exact hw _

theorem tailWeight_monotone {k : ℕ} {w : Fin (2 * k + 1) → ℝ}
    (hw : Monotone w) : Monotone (tailWeight w) := by
  intro i j hij
  apply hw
  change i.val + 1 ≤ j.val + 1
  omega

def tailLabel {k : ℕ} (x : Fin (2 * k + 1)) (hx0 : x ≠ 0) : Fin (2 * k) :=
  ⟨x.val - 1, by
    have hpos : 0 < x.val :=
      Nat.pos_of_ne_zero fun h ↦ hx0 (Fin.ext h)
    have hlt := x.isLt
    omega⟩

@[simp]
theorem tailLabel_val {k : ℕ} (x : Fin (2 * k + 1)) (hx0 : x ≠ 0) :
    (tailLabel x hx0).val = x.val - 1 := rfl

/-- If a near-perfect matching avoids zero, subtracting one from every used
label produces a perfect endpoint permutation of the tail. -/
noncomputable def tailEndpointEquiv {k : ℕ}
    (M : LabeledMatching (Fin (2 * k + 1)) k)
    (hzero : ∀ p, M.endpoints p ≠ 0) :
    (Fin k × Bool) ≃ Fin (2 * k) := by
  let f : Fin k × Bool → Fin (2 * k) := fun p ↦
    tailLabel (M.endpoints p) (hzero p)
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro p q hpq
    have hval := congrArg Fin.val hpq
    simp only [f, tailLabel_val] at hval
    have hp0 : 0 < (M.endpoints p).val :=
      Nat.pos_of_ne_zero fun h ↦ hzero p (Fin.ext h)
    have hq0 : 0 < (M.endpoints q).val :=
      Nat.pos_of_ne_zero fun h ↦ hzero q (Fin.ext h)
    apply M.endpoints.injective
    apply Fin.ext
    omega
  · simp [Fintype.card_prod, Nat.mul_comm]

theorem tailEndpointEquiv_weight {k : ℕ}
    (w : Fin (2 * k + 1) → ℝ)
    (M : LabeledMatching (Fin (2 * k + 1)) k)
    (hzero : ∀ p, M.endpoints p ≠ 0) (p : Fin k × Bool) :
    tailWeight w (tailEndpointEquiv M hzero p) = w (M.endpoints p) := by
  unfold tailWeight tailEndpointEquiv
  apply congrArg w
  apply Fin.ext
  simp only [Equiv.ofBijective_apply, tailLabel_val]
  have hpos : 0 < (M.endpoints p).val :=
    Nat.pos_of_ne_zero fun h ↦ hzero p (Fin.ext h)
  omega

theorem edgeMatchingProduct_eq_tailPairingProduct {k : ℕ}
    (w : Fin (2 * k + 1) → ℝ)
    (M : LabeledMatching (Fin (2 * k + 1)) k)
    (hzero : ∀ p, M.endpoints p ≠ 0) :
    edgeMatchingProduct w M =
      pairingProduct (tailWeight w) (tailEndpointEquiv M hzero) := by
  unfold edgeMatchingProduct pairingProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [tailEndpointEquiv_weight, tailEndpointEquiv_weight]
  rfl

/-- A codimension-one endpoint embedding has an unused label. -/
theorem exists_unusedLabel {k : ℕ}
    (M : LabeledMatching (Fin (2 * k + 1)) k) :
    ∃ u, ∀ p, M.endpoints p ≠ u := by
  by_contra h
  push_neg at h
  have hsurj : Function.Surjective M.endpoints := by
    intro u
    obtain ⟨p, hp⟩ := h u
    exact ⟨p, hp⟩
  have hcard := Fintype.card_le_of_surjective M.endpoints hsurj
  simp [Fintype.card_prod] at hcard
  omega

/-- Pointwise enlargement of positive vertex weights enlarges every exact
kernel matching product. -/
theorem edgeMatchingProduct_mono_pos {α : Type*} {k : ℕ}
    {w v : α → ℝ} (hw : ∀ a, 0 < w a)
    (M : LabeledMatching α k)
    (hwleft : ∀ i, w (M.left i) ≤ v (M.left i))
    (hwright : ∀ i, w (M.right i) ≤ v (M.right i)) :
    edgeMatchingProduct w M ≤ edgeMatchingProduct v M := by
  apply Finset.prod_le_prod
  · intro i _
    exact (edgeKernel_pos (hw _) (hw _)).le
  · intro i _
    have hleft :
        edgeKernel (w (M.left i)) (w (M.right i)) ≤
          edgeKernel (v (M.left i)) (w (M.right i)) :=
      edgeKernel_mono_left (u := w (M.left i)) (u' := v (M.left i))
        (v := w (M.right i)) (hw _).le (hw _).le (hwleft i)
        (add_pos (hw _) (hw _))
    have hright :
        edgeKernel (v (M.left i)) (w (M.right i)) ≤
          edgeKernel (v (M.left i)) (v (M.right i)) :=
      edgeKernel_mono_right (u := v (M.left i)) (v := w (M.right i))
        (v' := v (M.right i)) ((hw _).le.trans (hwleft i))
        (hw _).le (hwright i)
        (add_pos (lt_of_lt_of_le (hw (M.left i)) (hwleft i))
          (hw (M.right i)))
    exact hleft.trans hright

/-- Relabeling endpoints is the same as pulling the new weights back to the
old endpoint labels. -/
theorem edgeMatchingProduct_relabel {α β : Type*} {k : ℕ}
    (e : α ≃ β) (w : β → ℝ) (M : LabeledMatching α k) :
    edgeMatchingProduct w (M.relabel e) =
      edgeMatchingProduct (fun a ↦ w (e a)) M := by
  unfold edgeMatchingProduct
  rfl

/-- Exact outside-in domination for a near-perfect matching. -/
theorem edgeMatchingProduct_le_nearOutsideIn {k : ℕ}
    (w : Fin (2 * k + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (hmono : Monotone w) (M : LabeledMatching (Fin (2 * k + 1)) k) :
    edgeMatchingProduct w M ≤ outsideInProduct k (tailWeight w) := by
  obtain ⟨u, hu⟩ := exists_unusedLabel M
  let σ : Equiv.Perm (Fin (2 * k + 1)) := Equiv.swap 0 u
  let M' : LabeledMatching (Fin (2 * k + 1)) k := M.relabel σ
  have hweight (p : Fin k × Bool) :
      w (M.endpoints p) ≤ w (σ (M.endpoints p)) := by
    by_cases hp0 : M.endpoints p = 0
    · rw [hp0]
      apply hmono
      exact Fin.zero_le u
    · have hpu : M.endpoints p ≠ u := hu p
      rw [Equiv.swap_apply_of_ne_of_ne hp0 hpu]
  have hprod : edgeMatchingProduct w M ≤ edgeMatchingProduct w M' := by
    rw [edgeMatchingProduct_relabel]
    exact edgeMatchingProduct_mono_pos hw M
      (fun i ↦ hweight (i, false)) (fun i ↦ hweight (i, true))
  have hzero : ∀ p, M'.endpoints p ≠ 0 := by
    intro p hp
    have hsigma : σ (M.endpoints p) = 0 := hp
    have hpre : M.endpoints p = u := by
      change Equiv.swap 0 u (M.endpoints p) = 0 at hsigma
      have h := congrArg (Equiv.swap 0 u) hsigma
      simpa using h
    exact hu p hpre
  calc
    edgeMatchingProduct w M ≤ edgeMatchingProduct w M' := hprod
    _ = pairingProduct (tailWeight w) (tailEndpointEquiv M' hzero) :=
      edgeMatchingProduct_eq_tailPairingProduct w M' hzero
    _ ≤ outsideInProduct k (tailWeight w) :=
      pairingProduct_le_outsideIn (tailWeight w) (tailWeight_pos hw)
        (tailWeight_monotone hmono) (tailEndpointEquiv M' hzero)

end

end GDLowerBound.FourBlock
