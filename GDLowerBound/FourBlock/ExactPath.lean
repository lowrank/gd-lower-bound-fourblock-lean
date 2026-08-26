import GDLowerBound.FourBlock.CoupledEqualization
import GDLowerBound.FourBlock.KernelExchange
import GDLowerBound.Matching.TotalWeight

/-!
# Exact equalization on a finite chronological path

This module keeps the terminal factor explicit.  The internal factors are
exactly the envelope edge kernel; no asymptotic replacement is used.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Matching

noncomputable section

@[simp]
theorem delta_zero : delta 0 = 1 := by
  norm_num [delta]

@[simp]
theorem envelope_zero : envelope 0 = 1 := by
  norm_num [envelope]

theorem psi_le_two_edgeKernel {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    psi u v ≤ 2 * edgeKernel u v := by
  have hsum : 0 < u + v := by linarith
  have hb : 0 ≤ edgeParameter u v := edgeParameter_nonneg hu.le hv.le
  have hone := equalization_le_envelope hb (by norm_num : (0 : ℝ) < 1)
  have henv : 1 + edgeParameter u v ≤ envelope (edgeParameter u v) := by
    simpa using hone
  have hscale := mul_le_mul_of_nonneg_left henv hsum.le
  unfold psi edgeKernel edgeParameter at ⊢
  unfold edgeParameter at hscale
  field_simp [hsum.ne'] at hscale ⊢
  nlinarith

def pathA {n : ℕ} (xi : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 1 (fun i : Fin n ↦ xi i.castSucc + xi i.succ)

def pathB {n : ℕ} (xi : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun i : Fin n ↦ xi i.castSucc * xi i.succ)

def scaledPathWeight {n : ℕ} (D : ℝ) (xi : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ := fun i ↦ 2 * (D / (n + 1)) * xi i

theorem coupledEqualization_exactPath {n : ℕ} (D : ℝ)
    (hD : 0 < D) (u xi : Fin (n + 1) → ℝ)
    (hu : ∀ i, 0 < u i) (hxi : ∀ i, 0 < xi i)
    (hmass : ∑ i, u i ≤ D) :
    ∏ i, u i * (pathA xi i + pathB xi i * u i) ≤
      (D / (n + 1)) *
        ∏ i : Fin n,
          edgeKernel (scaledPathWeight D xi i.castSucc)
            (scaledPathWeight D xi i.succ) := by
  have hq : 0 < n + 1 := by omega
  have hA : ∀ i, 0 < pathA xi i := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [pathA]
    · simp only [pathA, Fin.lastCases_castSucc]
      exact add_pos (hxi _) (hxi _)
  have hB : ∀ i, 0 ≤ pathB xi i := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [pathB]
    · simp only [pathB, Fin.lastCases_castSucc]
      exact mul_nonneg (hxi _).le (hxi _).le
  have hcoupled := coupledEqualization hq u (pathA xi) (pathB xi) D
    hD hu hA hB hmass
  calc
    ∏ i, u i * (pathA xi i + pathB xi i * u i) ≤
        ∏ i, (D / (n + 1)) * pathA xi i *
          envelope ((D / (n + 1)) * pathB xi i / pathA xi i) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcoupled
    _ = (D / (n + 1)) *
        ∏ i : Fin n,
          edgeKernel (scaledPathWeight D xi i.castSucc)
            (scaledPathWeight D xi i.succ) := by
      rw [Fin.prod_univ_castSucc]
      simp only [pathA, pathB, Fin.lastCases_last]
      norm_num [envelope_zero]
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [pathA, pathB, Fin.lastCases_castSucc, scaledPathWeight]
      unfold edgeKernel edgeParameter
      have hqR : (0 : ℝ) < n + 1 := by exact_mod_cast hq
      have hubar : 0 < D / ((n : ℝ) + 1) := by positivity
      have hsum : 0 < xi i.castSucc + xi i.succ :=
        add_pos (hxi _) (hxi _)
      congr 1
      · ring
      · congr 1
        field_simp [hubar.ne', hsum.ne']

end

end GDLowerBound.FourBlock
