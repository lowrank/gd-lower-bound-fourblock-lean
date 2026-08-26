import GDLowerBound.FourBlock.CommonRigidityBudgets

/-!
# Normalized finite averaging composition

All schedule, rigidity, and error sums are divided by the same harmonic mass
of the sampled `m`-window.  Replacing a possibly negative finite mean deficit
by its positive part only increases the energy and rigidity right-hand sides.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def averagingHarmonicWeight (M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (M + 1) (N + 1), 1 / (m : ℝ)

theorem averagingHarmonicWeight_pos
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N) :
    0 < averagingHarmonicWeight M N := by
  unfold averagingHarmonicWeight
  apply Finset.sum_pos (fun m hm ↦ by
    have hmIco := Finset.mem_Ico.mp hm
    exact one_div_pos.mpr (by
      exact_mod_cast (show 0 < m by omega)))
  refine ⟨M + 1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩

def normalizedCommonSquareDeviation {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  commonSquareDeviationSum h M N / averagingHarmonicWeight M N

def normalizedCommonDefect {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  commonDefectSum h M N / averagingHarmonicWeight M N

def normalizedCommonMeanDeficit {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  commonMeanDeficitSum h M N / averagingHarmonicWeight M N

def effectiveMeanDeficit {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  max (normalizedCommonMeanDeficit h M N) 0

def effectiveMeanGrowth {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  betaLower - effectiveMeanDeficit h M N

def normalizedJointRigidityError {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  commonJointRigidityError h M N / averagingHarmonicWeight M N

def normalizedDefectRigidityError {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  commonDefectRigidityError h M N / averagingHarmonicWeight M N

def normalizedScheduleAveragingError (M N : ℕ) : ℝ :=
  scheduleAveragingFiniteError M N / averagingHarmonicWeight M N

/-- Once the effective finite mean growth reaches the target and the named
finite errors fit in the certified margin, the normalized averaged schedule
energy is strictly below the robust local gap. -/
theorem normalizedAveragedScheduleEnergy_lt_robustLocalGap
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 8 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h))
    (hgrowth : massExponent ≤ effectiveMeanGrowth h M N)
    (herrors :
      squareWeightSum * normalizedJointRigidityError h M N +
          defectSlackCoefficient * normalizedDefectRigidityError h M N +
          normalizedScheduleAveragingError M N < fourBlockFiniteMargin) :
    (∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ)) /
        averagingHarmonicWeight M N < robustLocalGap := by
  have hH : 0 < averagingHarmonicWeight M N :=
    averagingHarmonicWeight_pos (by omega) hMN
  have hMNle : M ≤ N := hMN.le
  have hcutCommon : CutoffConditions criticalP h (2 * M) (4 * N) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨hqIcc.1, hqIcc.2.trans h4N⟩)
  have henergyRaw := averagedScheduleEnergy_upper hQ hh hM hMNle
    hQ2M h4N hcut
  have henergyScaled := div_le_div_of_nonneg_right henergyRaw hH.le
  have henergy :
      (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ)) /
          averagingHarmonicWeight M N ≤
        averagedEnergyBudget (normalizedCommonSquareDeviation h M N)
            (normalizedCommonDefect h M N)
            (normalizedCommonMeanDeficit h M N) +
          normalizedScheduleAveragingError M N := by
    unfold normalizedCommonSquareDeviation normalizedCommonDefect
      normalizedCommonMeanDeficit normalizedScheduleAveragingError
    unfold averagedEnergyBudget logarithmicBlockCoefficient at henergyScaled ⊢
    ring_nf at henergyScaled ⊢
    exact henergyScaled
  have hjointRaw := commonMomentRigidityBudget hQ hh (by omega) hMNle
    hQ2M h4N hcut
  have hjointScaled := div_le_div_of_nonneg_right hjointRaw hH.le
  have hjoint :
      normalizedCommonSquareDeviation h M N +
          normalizedCommonDefect h M N / criticalTheta ≤
        2 * (betaLower + 1) * normalizedCommonMeanDeficit h M N +
          normalizedJointRigidityError h M N := by
    unfold normalizedCommonSquareDeviation normalizedCommonDefect
      normalizedCommonMeanDeficit normalizedJointRigidityError
    ring_nf at hjointScaled ⊢
    exact hjointScaled
  have hdefectRaw := commonSharpRigidityBudget hQ hh (by omega) hMNle
    hQ2M h4N hcut
  have hdefectScaled := div_le_div_of_nonneg_right hdefectRaw hH.le
  have hdefect :
      normalizedCommonDefect h M N ≤
        normalizedCommonMeanDeficit h M N / betaLower +
          normalizedDefectRigidityError h M N := by
    unfold normalizedCommonDefect normalizedCommonMeanDeficit
      normalizedDefectRigidityError
    ring_nf at hdefectScaled ⊢
    exact hdefectScaled
  have hEraw := commonDefectSum_nonneg hcutCommon
  have hE : 0 ≤ normalizedCommonDefect h M N := by
    unfold normalizedCommonDefect
    exact div_nonneg hEraw hH.le
  have hdle : normalizedCommonMeanDeficit h M N ≤
      effectiveMeanDeficit h M N := by
    unfold effectiveMeanDeficit
    exact le_max_left _ _
  have hd0 : 0 ≤ effectiveMeanDeficit h M N := by
    unfold effectiveMeanDeficit
    exact le_max_right _ _
  have hcoef : 0 ≤ 2 * (betaLower + 1) := by
    positivity [betaLower_pos]
  have hjointPlus :
      normalizedCommonSquareDeviation h M N +
          normalizedCommonDefect h M N / criticalTheta ≤
        2 * (betaLower + 1) * effectiveMeanDeficit h M N +
          normalizedJointRigidityError h M N := by
    have hm := mul_le_mul_of_nonneg_left hdle hcoef
    linarith
  have hdefectPlus :
      normalizedCommonDefect h M N ≤
        effectiveMeanDeficit h M N / betaLower +
          normalizedDefectRigidityError h M N := by
    have hm := div_le_div_of_nonneg_right hdle betaLower_pos.le
    linarith
  have hgammaHi : effectiveMeanGrowth h M N ≤ betaLower := by
    unfold effectiveMeanGrowth
    linarith
  have hglobal := averagedEnergyBudget_add_errors_lt_robustLocalGap
    hE hgrowth hgammaHi
    (by simpa [effectiveMeanGrowth] using hjointPlus)
    (by simpa [effectiveMeanGrowth] using hdefectPlus) herrors
  have hlogCoeff : 0 ≤ logarithmicBlockCoefficient := by
    unfold logarithmicBlockCoefficient lambdaTwo lambdaThree
    have h32 : 0 ≤ Real.log (3 / 2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    have h43 : 0 ≤ Real.log (4 / 3 : ℝ) :=
      Real.log_nonneg (by norm_num)
    positivity
  have hbudgetMono :
      averagedEnergyBudget (normalizedCommonSquareDeviation h M N)
          (normalizedCommonDefect h M N)
          (normalizedCommonMeanDeficit h M N) ≤
        averagedEnergyBudget (normalizedCommonSquareDeviation h M N)
          (normalizedCommonDefect h M N)
          (effectiveMeanDeficit h M N) := by
    unfold averagedEnergyBudget
    have hm := mul_le_mul_of_nonneg_left hdle hlogCoeff
    linarith
  have hglobal' :
      averagedEnergyBudget (normalizedCommonSquareDeviation h M N)
          (normalizedCommonDefect h M N) (effectiveMeanDeficit h M N) +
        normalizedScheduleAveragingError M N < robustLocalGap := by
    simpa [effectiveMeanGrowth] using hglobal
  linarith

end

end GDLowerBound.FourBlock
