import GDLowerBound.FourBlock.ExactMatching
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Outside-in order for perfect exact-kernel matchings

The nonlinear part of the four-block argument is the following finite fact:
on a sorted list of `2*k` positive weights, every perfect matching is
dominated by the outside-in matching.  We work additively with `logKernel`;
positivity then recovers the product statement by exponentiation.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

def pairingLogScore {k : ℕ} (w : Fin (2 * k) → ℝ)
    (e : (Fin k × Bool) ≃ Fin (2 * k)) : ℝ :=
  ∑ i : Fin k,
    logKernel (w (e (i, false))) (w (e (i, true)))

def pairingProduct {k : ℕ} (w : Fin (2 * k) → ℝ)
    (e : (Fin k × Bool) ≃ Fin (2 * k)) : ℝ :=
  ∏ i : Fin k,
    edgeKernel (w (e (i, false))) (w (e (i, true)))

def outsideInLeft (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨i, by omega⟩

def outsideInRight (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨2 * k - 1 - i, by omega⟩

def outsideInLogScore (k : ℕ) (w : Fin (2 * k) → ℝ) : ℝ :=
  ∑ i : Fin k, logKernel (w (outsideInLeft k i)) (w (outsideInRight k i))

def outsideInProduct (k : ℕ) (w : Fin (2 * k) → ℝ) : ℝ :=
  ∏ i : Fin k, edgeKernel (w (outsideInLeft k i)) (w (outsideInRight k i))

theorem logKernel_exchange_parallel_le
    {a b c d : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hb : 0 < b) (hbd : b ≤ d) :
    logKernel a b + logKernel c d ≤ logKernel a d + logKernel b c := by
  have hc : 0 < c := ha.trans_le hac
  have hd : 0 < d := hb.trans_le hbd
  have h := pairLogKernelClosed_exchange_parallel_le ha hac hb hbd
  rw [pairLogKernelClosed_eq ⟨ha, hb⟩,
    pairLogKernelClosed_eq ⟨hc, hd⟩,
    pairLogKernelClosed_eq ⟨ha, hd⟩,
    pairLogKernelClosed_eq ⟨hb, hc⟩] at h
  exact h

/-- Replace two summands, leaving every other summand unchanged. -/
theorem sum_le_sum_of_eq_off_two {n : ℕ} (f g : Fin n → ℝ)
    {a b : Fin n} (hab : a ≠ b)
    (hpair : f a + f b ≤ g a + g b)
    (hoff : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    ∑ i, f i ≤ ∑ i, g i := by
  classical
  let s : Finset (Fin n) := (Finset.univ.erase a).erase b
  have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ.erase a : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hfa :
      ∑ i, f i = (∑ i ∈ s, f i) + f b + f a := by
    dsimp only [s]
    rw [Finset.sum_erase_add _ _ hb, Finset.sum_erase_add _ _ ha]
  have hga :
      ∑ i, g i = (∑ i ∈ s, g i) + g b + g a := by
    dsimp only [s]
    rw [Finset.sum_erase_add _ _ hb, Finset.sum_erase_add _ _ ha]
  have hrest : (∑ i ∈ s, f i) = ∑ i ∈ s, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    exact hoff i hi''.1 hi'.1
  rw [hfa, hga, hrest]
  linarith

def innerWeight {k : ℕ} (w : Fin (2 * (k + 1)) → ℝ) : Fin (2 * k) → ℝ :=
  fun i ↦ w ⟨i + 1, by omega⟩

theorem innerWeight_pos {k : ℕ} {w : Fin (2 * (k + 1)) → ℝ}
    (hw : ∀ i, 0 < w i) : ∀ i, 0 < innerWeight w i := by
  intro i
  exact hw _

theorem innerWeight_monotone {k : ℕ} {w : Fin (2 * (k + 1)) → ℝ}
    (hw : Monotone w) : Monotone (innerWeight w) := by
  intro i j hij
  apply hw
  change i.val + 1 ≤ j.val + 1
  omega

def outerLast (k : ℕ) : Fin (2 * (k + 1)) :=
  ⟨2 * (k + 1) - 1, by omega⟩

theorem outsideInLogScore_succ {k : ℕ} (w : Fin (2 * (k + 1)) → ℝ) :
    outsideInLogScore (k + 1) w =
      logKernel (w 0) (w (outerLast k)) +
        outsideInLogScore k (innerWeight w) := by
  rw [outsideInLogScore, Fin.sum_univ_succ]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · apply congrArg₂ logKernel <;> apply congrArg w <;> apply Fin.ext <;>
      simp [outsideInLeft, outsideInRight, outerLast]
  · unfold outsideInLogScore innerWeight outsideInLeft outsideInRight
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg₂ logKernel <;> apply congrArg w <;> apply Fin.ext <;> simp
    omega

theorem pairingProduct_eq_exp_logScore {k : ℕ}
    {w : Fin (2 * k) → ℝ} (hw : ∀ i, 0 < w i)
    (e : (Fin k × Bool) ≃ Fin (2 * k)) :
    pairingProduct w e = Real.exp (pairingLogScore w e) := by
  unfold pairingProduct pairingLogScore
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [logKernel_eq_log_edgeKernel (hw _).le (hw _).le (add_pos (hw _) (hw _))]
  rw [Real.exp_log]
  exact edgeKernel_pos (hw _) (hw _)

theorem outsideInProduct_eq_exp_logScore {k : ℕ}
    {w : Fin (2 * k) → ℝ} (hw : ∀ i, 0 < w i) :
    outsideInProduct k w = Real.exp (outsideInLogScore k w) := by
  unfold outsideInProduct outsideInLogScore
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [logKernel_eq_log_edgeKernel (hw _).le (hw _).le (add_pos (hw _) (hw _))]
  rw [Real.exp_log]
  exact edgeKernel_pos (hw _) (hw _)

end

end GDLowerBound.FourBlock
