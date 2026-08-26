import GDLowerBound.FourBlock.AutoSqrt
import GDLowerBound.FourBlock.KernelCertificate

/-!
# Automatic rational upper bounds for the logarithmic edge kernel

The checker computes a Newton upper bound for the only square root in the
closed kernel formula, then uses the proved atanh-series logarithm bound.
Thus a certificate node contains only rational endpoints and two small
iteration counts.
-/

namespace GDLowerBound.FourBlock

def qAutoDeltaLower (b : ℚ) (sqrtSteps : ℕ) : ℚ :=
  2 / (2 * b + 1 + qSqrtNewtonUpper (4 * b ^ 2 + 1) sqrtSteps)

def qAutoDeltaUpper (b : ℚ) : ℚ := 1 / (b + 1)

def qKernelUpperAuto (u v : ℚ) (sqrtSteps logSteps : ℕ) : ℚ :=
  let b := qEdgeParameter u v
  let dlo := qAutoDeltaLower b sqrtSteps
  qLogUpper ((u + v) / 2) logSteps +
    qLogUpper (2 / dlo - 1) logSteps + qAutoDeltaUpper b - 1

theorem qAutoDeltaLower_pos {b : ℚ} (hb : 0 ≤ b) (n : ℕ) :
    0 < qAutoDeltaLower b n := by
  have hx : (1 : ℚ) ≤ 4 * b ^ 2 + 1 := by nlinarith [sq_nonneg b]
  have hu := (qSqrtNewtonUpper_valid hx n).1
  unfold qAutoDeltaLower
  positivity

theorem qAutoDeltaLower_le_one {b : ℚ} (hb : 0 ≤ b) (n : ℕ) :
    qAutoDeltaLower b n ≤ 1 := by
  have hx : (1 : ℚ) ≤ 4 * b ^ 2 + 1 := by nlinarith [sq_nonneg b]
  have huValid := qSqrtNewtonUpper_valid hx n
  have huOne : (1 : ℚ) ≤ qSqrtNewtonUpper (4 * b ^ 2 + 1) n := by
    nlinarith
  have hden : (0 : ℚ) <
      2 * b + 1 + qSqrtNewtonUpper (4 * b ^ 2 + 1) n := by positivity
  unfold qAutoDeltaLower
  apply (div_le_iff₀ hden).2
  linarith

theorem qAutoFactor_pos {b : ℚ} (hb : 0 ≤ b) (n : ℕ) :
    0 < 2 / qAutoDeltaLower b n - 1 := by
  have hd0 := qAutoDeltaLower_pos hb n
  have hd1 := qAutoDeltaLower_le_one hb n
  rw [sub_pos, lt_div_iff₀ hd0]
  linarith

theorem qKernelUpperAuto_sound {u v : ℚ} (huq : 0 < u) (hvq : 0 < v)
    (sqrtSteps logSteps : ℕ) :
    logKernel (u : ℝ) (v : ℝ) ≤
      (qKernelUpperAuto u v sqrtSteps logSteps : ℝ) := by
  let bq := qEdgeParameter u v
  let xq : ℚ := 4 * bq ^ 2 + 1
  let uq : ℚ := qSqrtNewtonUpper xq sqrtSteps
  let dloq : ℚ := qAutoDeltaLower bq sqrtSteps
  let dupq : ℚ := qAutoDeltaUpper bq
  have hu : (0 : ℝ) < u := by exact_mod_cast huq
  have hv : (0 : ℝ) < v := by exact_mod_cast hvq
  have hsum : (0 : ℝ) < u + v := by positivity
  have hbq : (0 : ℚ) ≤ bq := by
    unfold bq qEdgeParameter
    positivity
  have hb : 0 ≤ edgeParameter (u : ℝ) (v : ℝ) :=
    edgeParameter_nonneg hu.le hv.le
  have hxq : (1 : ℚ) ≤ xq := by
    dsimp only [xq]
    nlinarith [sq_nonneg bq]
  have huUpper := qSqrtNewtonUpper_sound hxq sqrtSteps
  have hxu : (xq : ℝ) =
      4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1 := by
    dsimp only [xq, bq]
    push_cast
    rw [coe_qEdgeParameter]
  rw [hxu] at huUpper
  have hdloq : 0 < dloq := by
    exact qAutoDeltaLower_pos hbq sqrtSteps
  have hdenActual : 0 <
      2 * edgeParameter (u : ℝ) (v : ℝ) + 1 +
        Real.sqrt (4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1) :=
    delta_denominator_pos hb
  have hdenUpper : 0 <
      2 * edgeParameter (u : ℝ) (v : ℝ) + 1 + (uq : ℝ) := by
    have huqPos := (qSqrtNewtonUpper_valid hxq sqrtSteps).1
    have huqPosR : (0 : ℝ) < uq := by exact_mod_cast huqPos
    positivity
  have hdLower : (dloq : ℝ) ≤
      delta (edgeParameter (u : ℝ) (v : ℝ)) := by
    have hdenLe :
        2 * edgeParameter (u : ℝ) (v : ℝ) + 1 +
            Real.sqrt (4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1) ≤
          2 * edgeParameter (u : ℝ) (v : ℝ) + 1 + (uq : ℝ) := by
      linarith
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      hdenActual hdenLe
    unfold delta
    have hdloEq : (dloq : ℝ) =
        2 / (2 * edgeParameter (u : ℝ) (v : ℝ) + 1 + (uq : ℝ)) := by
      dsimp only [dloq, qAutoDeltaLower, uq, xq, bq]
      push_cast
      rw [coe_qEdgeParameter]
    rw [hdloEq]
    exact hfrac
  have hsqrtOne : (1 : ℝ) ≤
      Real.sqrt (4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1) := by
    have hsqrt0 := Real.sqrt_nonneg
      (4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1)
    have hsqrtSq := Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1)
    nlinarith
  have hbplus : 0 < edgeParameter (u : ℝ) (v : ℝ) + 1 := by positivity
  have hdUpper : delta (edgeParameter (u : ℝ) (v : ℝ)) ≤ (dupq : ℝ) := by
    have hdenLe : 2 * (edgeParameter (u : ℝ) (v : ℝ) + 1) ≤
        2 * edgeParameter (u : ℝ) (v : ℝ) + 1 +
          Real.sqrt (4 * edgeParameter (u : ℝ) (v : ℝ) ^ 2 + 1) := by
      linarith
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) < 2 * (edgeParameter (u : ℝ) (v : ℝ) + 1))
      hdenLe
    have hdupEq : (dupq : ℝ) =
        2 / (2 * (edgeParameter (u : ℝ) (v : ℝ) + 1)) := by
      dsimp only [dupq, qAutoDeltaUpper, bq]
      push_cast
      rw [coe_qEdgeParameter]
      field_simp [hbplus.ne']
    unfold delta
    rw [hdupEq]
    exact hfrac
  have hdeltaPos := delta_pos hb
  have hfactorPos : 0 <
      2 / delta (edgeParameter (u : ℝ) (v : ℝ)) - 1 := by
    have hd1 := delta_le_one hb
    rw [sub_pos, lt_div_iff₀ hdeltaPos]
    nlinarith
  have hfactorAutoPosQ : (0 : ℚ) < 2 / dloq - 1 := by
    exact qAutoFactor_pos hbq sqrtSteps
  have hfactorAutoPos : (0 : ℝ) < 2 / (dloq : ℝ) - 1 := by
    exact_mod_cast hfactorAutoPosQ
  have hfactorLe :
      2 / delta (edgeParameter (u : ℝ) (v : ℝ)) - 1 ≤
        2 / (dloq : ℝ) - 1 := by
    have hdloR : (0 : ℝ) < dloq := by exact_mod_cast hdloq
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      hdloR hdLower
    linarith
  have hlogTotal := le_logUpper
    (y := (((u + v) / 2 : ℚ) : ℝ)) (by exact_mod_cast (by positivity :
      (0 : ℚ) < (u + v) / 2)) logSteps
  rw [← coe_qLogUpper] at hlogTotal
  push_cast at hlogTotal
  have hlogFactorAuto := le_logUpper
    (y := ((2 / dloq - 1 : ℚ) : ℝ)) (by exact_mod_cast hfactorAutoPosQ) logSteps
  rw [← coe_qLogUpper] at hlogFactorAuto
  push_cast at hlogFactorAuto
  have hlogFactor :
      Real.log (2 / delta (edgeParameter (u : ℝ) (v : ℝ)) - 1) ≤
        (qLogUpper (2 / dloq - 1) logSteps : ℝ) := by
    exact (Real.log_le_log hfactorPos hfactorLe).trans hlogFactorAuto
  rw [logKernel_closed hu.le hv.le hsum]
  dsimp only [qKernelUpperAuto]
  push_cast
  dsimp only [dloq, dupq, bq] at hdUpper hlogFactor ⊢
  linarith

end GDLowerBound.FourBlock
