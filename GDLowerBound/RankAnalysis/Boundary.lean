import GDLowerBound.RankAnalysis.Adjacent
import GDLowerBound.RankAnalysis.Lyapunov

namespace GDLowerBound
namespace RankAnalysis

open scoped BigOperators Real
open Schedule

noncomputable section

/-- The scalar consequences of the manuscript's large-product alternative on
an interval of ranks.  This deliberately separates the propagation argument
from the matching theorem that supplies these inequalities. -/
def CutoffConditions {T : ℕ} (p : ℝ) (h : StepSchedule T)
    (lo hi : ℕ) : Prop :=
  ∀ q ∈ Finset.Icc lo hi,
    lyapunovTheta p < zetaState h q ∧
      0 < relativeMassIncrement h q ∧
      relativeMassIncrement h q < (lyapunovTheta p)⁻¹ ∧
      zetaState h q * relativeMassIncrement h q ≤ 1

/-- A reversed cutoff interval carries no hypotheses. -/
theorem cutoffConditions_of_hi_lt_lo {T : ℕ} (p : ℝ)
    (h : StepSchedule T) {lo hi : ℕ} (hlt : hi < lo) :
    CutoffConditions p h lo hi := by
  intro q hq
  have hqIcc := Finset.mem_Icc.mp hq
  omega

/-- The rank-independent exponent accumulated by Lyapunov propagation. -/
def boundaryErrorConstant (p : ℝ) : ℝ :=
  1 / (lyapunovTheta p * (p + 1)) +
    oneStepLyapunovConstant p * (Real.pi ^ 2 / 6)

/-- The explicit constant `K_p` in the boundary-propagation lemma. -/
def boundaryPropagationConstant (p : ℝ) : ℝ :=
  2 * Real.exp (boundaryErrorConstant p)

/-- The Lyapunov potential evaluated at rank `q`. -/
def rankLyapunov {T : ℕ} (p : ℝ) (h : StepSchedule T) (q : ℕ) : ℝ :=
  lyapunovPotential p (relativeMassIncrement h q) (zetaState h q)

theorem boundaryErrorConstant_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ boundaryErrorConstant p := by
  have htheta0 := lyapunovTheta_pos hp
  have hp10 : 0 < p + 1 := by linarith
  have hC := oneStepLyapunovConstant_ge_one p
  unfold boundaryErrorConstant
  positivity

theorem boundaryPropagationConstant_ge_one {p : ℝ} (hp : 1 < p) :
    1 ≤ boundaryPropagationConstant p := by
  have hA := boundaryErrorConstant_nonneg hp
  have hexp : 1 ≤ Real.exp (boundaryErrorConstant p) :=
    (Real.one_le_exp_iff.mpr hA)
  unfold boundaryPropagationConstant
  nlinarith

private lemma sum_adjacent_sub
    (f : ℕ → ℝ) {k r : ℕ} (hkr : k ≤ r) :
    ∑ n ∈ Finset.Ico (k + 1) (r + 1), (f (n - 1) - f n) =
      f k - f r := by
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ r hkr ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      rw [ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Integral comparison for the exact harmonic interval used in the proof. -/
private lemma sum_inv_Ico_le_log_div {ell r : ℕ}
    (hell0 : 1 ≤ ell) (hellr : ell ≤ r) :
    ∑ n ∈ Finset.Ico (ell + 1) (r + 1), (1 / (n : ℝ)) ≤
      Real.log ((r : ℝ) / (ell : ℝ)) := by
  have hterm : ∀ n ∈ Finset.Ico (ell + 1) (r + 1),
      (1 / (n : ℝ)) ≤
        Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn2 : 2 ≤ n := by omega
    have hnR0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1R0 : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    have hx : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) :=
      div_pos hnR0 hn1R0
    have hlog := Real.one_sub_inv_le_log_of_pos hx
    have hid :
        1 / (n : ℝ) =
          1 - ((n : ℝ) / ((n - 1 : ℕ) : ℝ))⁻¹ := by
      field_simp [ne_of_gt hnR0, ne_of_gt hn1R0]
      norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
    rw [hid]
    exact hlog
  calc
    ∑ n ∈ Finset.Ico (ell + 1) (r + 1), (1 / (n : ℝ)) ≤
        ∑ n ∈ Finset.Ico (ell + 1) (r + 1),
          Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum hterm
    _ = ∑ n ∈ Finset.Ico (ell + 1) (r + 1),
          (Real.log (n : ℝ) - Real.log (n - 1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnIco := Finset.mem_Ico.mp hn
      rw [Real.log_div
        (by exact_mod_cast (by omega : n ≠ 0))
        (by exact_mod_cast (by omega : n - 1 ≠ 0))]
    _ = Real.log (r : ℝ) - Real.log (ell : ℝ) := by
      calc
        ∑ n ∈ Finset.Ico (ell + 1) (r + 1),
            (Real.log (n : ℝ) - Real.log (n - 1 : ℕ)) =
          -∑ n ∈ Finset.Ico (ell + 1) (r + 1),
            (Real.log (n - 1 : ℕ) - Real.log (n : ℝ)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro n _
              ring
        _ = -(Real.log (ell : ℝ) - Real.log (r : ℝ)) := by
          rw [sum_adjacent_sub (fun n ↦ Real.log (n : ℝ)) hellr]
        _ = Real.log (r : ℝ) - Real.log (ell : ℝ) := by ring
    _ = Real.log ((r : ℝ) / (ell : ℝ)) := by
      have hellNe : (ell : ℝ) ≠ 0 := by exact_mod_cast (by omega : ell ≠ 0)
      have hrNe : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      rw [Real.log_div hrNe hellNe]

/-- Every finite interval of reciprocal squares is bounded by the Basel sum. -/
private lemma sum_inv_sq_Ico_le_pi {ell r : ℕ} :
    ∑ n ∈ Finset.Ico (ell + 1) (r + 1), (1 / (n : ℝ) ^ 2) ≤
      Real.pi ^ 2 / 6 := by
  calc
    ∑ n ∈ Finset.Ico (ell + 1) (r + 1), (1 / (n : ℝ) ^ 2) ≤
        ∑' n : ℕ, (1 / (n : ℝ) ^ 2) := by
      exact hasSum_zeta_two.summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

/-- The Lyapunov potential is nonnegative and uniformly bounded at every
rank satisfying the cutoff conditions. -/
private lemma potential_bounds
    {T : ℕ} {p : ℝ} (hp : 1 < p) {h : StepSchedule T}
    {lo hi q : ℕ} (hcut : CutoffConditions p h lo hi)
    (hq : q ∈ Finset.Icc lo hi) :
    0 ≤ lyapunovPotential p (relativeMassIncrement h q) (zetaState h q) ∧
      lyapunovPotential p (relativeMassIncrement h q) (zetaState h q) ≤
        1 / (lyapunovTheta p * (p + 1)) := by
  obtain ⟨hz, hnu0, hnuB, hdensity⟩ := hcut q hq
  have htheta0 := lyapunovTheta_pos hp
  have hp10 : 0 < p + 1 := by linarith
  have hnuDen0 : 0 < relativeMassIncrement h q + p + 1 := by linarith
  have hden0 :
      0 < lyapunovTheta p * (relativeMassIncrement h q + p + 1) :=
    mul_pos htheta0 hnuDen0
  unfold lyapunovPotential lyapunovCoeff
  constructor
  · positivity
  · calc
      relativeMassIncrement h q /
          (lyapunovTheta p * (relativeMassIncrement h q + p + 1)) *
          (zetaState h q - lyapunovTheta p) =
        relativeMassIncrement h q * (zetaState h q - lyapunovTheta p) /
          (lyapunovTheta p * (relativeMassIncrement h q + p + 1)) := by ring
      _ ≤ relativeMassIncrement h q * zetaState h q /
          (lyapunovTheta p * (relativeMassIncrement h q + p + 1)) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        exact mul_le_mul_of_nonneg_left (sub_le_self _ htheta0.le) hnu0.le
      _ ≤ 1 / (lyapunovTheta p * (relativeMassIncrement h q + p + 1)) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        nlinarith
      _ ≤ 1 / (lyapunovTheta p * (p + 1)) := by
        apply one_div_le_one_div_of_le (mul_pos htheta0 hp10)
        exact mul_le_mul_of_nonneg_left (by linarith) htheta0.le

/-- On a cutoff interval, the adjacent-rank identities provide every
hypothesis of the scalar one-step Lyapunov theorem. -/
private lemma oneStep_of_cutoff
    {T : ℕ} {p : ℝ} (hp : 1 < p) {Q : ℕ}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell n : ℕ} (hQell : Q ≤ ell)
    (hcut : CutoffConditions p h ell (longCount h))
    (hn : n ∈ Finset.Ico (ell + 1) (longCount h + 1)) :
    rankLyapunov p h n - rankLyapunov p h (n - 1) ≤
      (p - 1 - relativeMassIncrement h n) / (n : ℝ) +
        oneStepLyapunovConstant p / (n : ℝ) ^ 2 := by
  have hnIco := Finset.mem_Ico.mp hn
  have hthetaInv0 : 0 < (lyapunovTheta p)⁻¹ := inv_pos.mpr (lyapunovTheta_pos hp)
  have hQR0 : 0 < (Q : ℝ) := hthetaInv0.trans hQ
  have hQnat : 1 ≤ Q := by exact_mod_cast hQR0
  have hn_le : n ≤ longCount h := by omega
  have hnprev0 : 1 ≤ n - 1 := by omega
  have hnprev_lt : n - 1 < longCount h := by omega
  have hnprev_mem : n - 1 ∈ Finset.Icc ell (longCount h) := by
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hn_mem : n ∈ Finset.Icc ell (longCount h) := by
    exact Finset.mem_Icc.mpr ⟨by omega, hn_le⟩
  obtain ⟨hzPrev, hu0, huB, _huDensity⟩ := hcut (n - 1) hnprev_mem
  obtain ⟨_hzNext, hv0, hvB, _hvDensity⟩ := hcut n hn_mem
  have hnR : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hN : p ^ 2 - 1 < (n : ℝ) - 1 := by
    rw [← lyapunovTheta_inv p]
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast (by omega : Q ≤ n - 1)
    exact hQ.trans_le (hQcast.trans_eq hnR)
  have hsmall :
      relativeMassIncrement h (n - 1) < ((n - 1 : ℕ) : ℝ) := by
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast (by omega : Q ≤ n - 1)
    exact huB.trans (hQ.trans_le hQcast)
  have hmass := massIncrementBound hh hnprev0 hnprev_lt hsmall
  have hzrec := zetaRecursion hh hnprev0 hnprev_lt
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnSucc] at hmass hzrec
  have hzNext :
      zetaState h n =
        lyapunovOmega (n : ℝ) (relativeMassIncrement h n) *
            zetaState h (n - 1) +
          1 / ((n : ℝ) * relativeMassIncrement h n) := by
    simpa [lyapunovOmega, hnR, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hzrec
  unfold rankLyapunov
  apply oneStepLyapunov hp (by omega : 2 ≤ n) hN
  · exact hu0
  · simpa only [lyapunovTheta_inv] using huB.le
  · exact hv0
  · simpa only [lyapunovTheta_inv] using hvB.le
  · exact hzPrev.le
  · simpa [hnR] using hmass
  · exact hzNext

/-- Telescoping the one-step estimate over a cutoff interval. -/
private lemma sum_increment_le
    {T : ℕ} {p : ℝ} (hp : 1 < p) {Q : ℕ}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell : ℕ} (hQell : Q ≤ ell) (hellr : ell ≤ longCount h)
    (hcut : CutoffConditions p h ell (longCount h)) :
    ∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
        relativeMassIncrement h n / (n : ℝ) ≤
      (p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ)) +
        boundaryErrorConstant p := by
  have hthetaInv0 : 0 < (lyapunovTheta p)⁻¹ := inv_pos.mpr (lyapunovTheta_pos hp)
  have hQR0 : 0 < (Q : ℝ) := hthetaInv0.trans hQ
  have hQnat : 1 ≤ Q := by exact_mod_cast hQR0
  have hell0 : 1 ≤ ell := hQnat.trans hQell
  have hstep : ∀ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
      relativeMassIncrement h n / (n : ℝ) ≤
        (p - 1) / (n : ℝ) +
          oneStepLyapunovConstant p / (n : ℝ) ^ 2 +
          (rankLyapunov p h (n - 1) - rankLyapunov p h n) := by
    intro n hn
    have hone := oneStep_of_cutoff hp hQ hh hQell hcut hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hrewrite :
        (p - 1 - relativeMassIncrement h n) / (n : ℝ) =
          (p - 1) / (n : ℝ) -
            relativeMassIncrement h n / (n : ℝ) := by ring
    rw [hrewrite] at hone
    linarith
  have hsum := Finset.sum_le_sum hstep
  have htelescope :=
    sum_adjacent_sub (rankLyapunov p h) hellr
  have hsumExact :
      ∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          ((p - 1) / (n : ℝ) +
            oneStepLyapunovConstant p / (n : ℝ) ^ 2 +
            (rankLyapunov p h (n - 1) - rankLyapunov p h n)) =
        (p - 1) *
            (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
              1 / (n : ℝ)) +
          oneStepLyapunovConstant p *
            (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
              1 / (n : ℝ) ^ 2) +
          (rankLyapunov p h ell - rankLyapunov p h (longCount h)) := by
    simp_rw [Finset.sum_add_distrib]
    rw [htelescope]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp
  have hharm := sum_inv_Ico_le_log_div hell0 hellr
  have hsq := sum_inv_sq_Ico_le_pi (ell := ell) (r := longCount h)
  have hpotEll := potential_bounds hp hcut
    (Finset.mem_Icc.mpr ⟨le_rfl, hellr⟩)
  have hpotR := potential_bounds hp hcut
    (Finset.mem_Icc.mpr ⟨hellr, le_rfl⟩)
  have hpot :
      rankLyapunov p h ell - rankLyapunov p h (longCount h) ≤
        1 / (lyapunovTheta p * (p + 1)) := by
    unfold rankLyapunov
    linarith [hpotEll.2, hpotR.1]
  have hharmScaled := mul_le_mul_of_nonneg_left hharm (by linarith : 0 ≤ p - 1)
  have hsqScaled := mul_le_mul_of_nonneg_left hsq
    ((oneStepLyapunovConstant_ge_one p).trans' zero_le_one)
  calc
    ∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
        relativeMassIncrement h n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          ((p - 1) / (n : ℝ) +
            oneStepLyapunovConstant p / (n : ℝ) ^ 2 +
            (rankLyapunov p h (n - 1) - rankLyapunov p h n)) := hsum
    _ = (p - 1) *
            (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
              1 / (n : ℝ)) +
          oneStepLyapunovConstant p *
            (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
              1 / (n : ℝ) ^ 2) +
          (rankLyapunov p h ell - rankLyapunov p h (longCount h)) := hsumExact
    _ ≤ (p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ)) +
          oneStepLyapunovConstant p * (Real.pi ^ 2 / 6) +
          1 / (lyapunovTheta p * (p + 1)) := by
      exact add_le_add (add_le_add hharmScaled hsqScaled) hpot
    _ = (p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ)) +
          boundaryErrorConstant p := by
      unfold boundaryErrorConstant
      ring

/-- Product-to-exponential conversion after the Lyapunov sum has been
telescoped. -/
private lemma intervalMassRatio_le
    {T : ℕ} {p : ℝ} (hp : 1 < p) {Q : ℕ}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell : ℕ} (hQell : Q ≤ ell) (hellr : ell ≤ longCount h)
    (hcut : CutoffConditions p h ell (longCount h)) :
    unresolvedMass h ell / cappedMass h ≤
      Real.exp (boundaryErrorConstant p) *
        (((longCount h : ℝ) / (ell : ℝ)) ^ (p - 1)) := by
  have hthetaInv0 : 0 < (lyapunovTheta p)⁻¹ := inv_pos.mpr (lyapunovTheta_pos hp)
  have hQR0 : 0 < (Q : ℝ) := hthetaInv0.trans hQ
  have hQnat : 1 ≤ Q := by exact_mod_cast hQR0
  have hell0 : 1 ≤ ell := hQnat.trans hQell
  have hr0 : 0 < longCount h := lt_of_lt_of_le (by omega : 0 < ell) hellr
  have hellR0 : 0 < (ell : ℝ) := by exact_mod_cast (by omega : 0 < ell)
  have hrR0 : 0 < (longCount h : ℝ) := by exact_mod_cast hr0
  have hratio0 : 0 < (longCount h : ℝ) / (ell : ℝ) :=
    div_pos hrR0 hellR0
  have hsum := sum_increment_le hp hQ hh hQell hellr hcut
  have hprod :
      ∏ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          (1 + relativeMassIncrement h n / (n : ℝ)) ≤
        Real.exp
          (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
            relativeMassIncrement h n / (n : ℝ)) := by
    calc
      ∏ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          (1 + relativeMassIncrement h n / (n : ℝ)) ≤
        ∏ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          Real.exp (relativeMassIncrement h n / (n : ℝ)) := by
        apply Finset.prod_le_prod
        · intro n hn
          have hnIco := Finset.mem_Ico.mp hn
          have hnmem : n ∈ Finset.Icc ell (longCount h) :=
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hnu := (hcut n hnmem).2.1
          positivity
        · intro n hn
          simpa [add_comm] using
            Real.add_one_le_exp (relativeMassIncrement h n / (n : ℝ))
      _ = Real.exp
          (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
            relativeMassIncrement h n / (n : ℝ)) := by
        rw [Real.exp_sum]
  calc
    unresolvedMass h ell / cappedMass h =
        ∏ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          (1 + relativeMassIncrement h n / (n : ℝ)) := massProduct hh hellr
    _ ≤ Real.exp
          (∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
            relativeMassIncrement h n / (n : ℝ)) := hprod
    _ ≤ Real.exp
          ((p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ)) +
            boundaryErrorConstant p) := Real.exp_le_exp.mpr hsum
    _ = Real.exp (boundaryErrorConstant p) *
        (((longCount h : ℝ) / (ell : ℝ)) ^ (p - 1)) := by
      calc
        Real.exp
            ((p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ)) +
              boundaryErrorConstant p) =
          Real.exp
              ((p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ))) *
            Real.exp (boundaryErrorConstant p) := Real.exp_add _ _
        _ = Real.exp (boundaryErrorConstant p) *
            Real.exp
              ((p - 1) * Real.log ((longCount h : ℝ) / (ell : ℝ))) :=
          mul_comm _ _
        _ = Real.exp (boundaryErrorConstant p) *
            (((longCount h : ℝ) / (ell : ℝ)) ^ (p - 1)) := by
          rw [Real.rpow_def_of_pos hratio0]
          congr 2
          ring

/-- The core propagation estimate, corresponding to
`eq:core-propagation`.  When `ell = r`, no cutoff condition is required. -/
theorem coreBoundaryPropagation
    {T : ℕ} {p : ℝ} (hp : 1 < p) {Q : ℕ}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell : ℕ} (hQell : Q ≤ ell) (hellr : ell ≤ longCount h)
    (hcut : ell < longCount h → CutoffConditions p h ell (longCount h)) :
    unresolvedMass h ell * ((ell : ℝ) ^ (p - 1)) ≤
      (boundaryPropagationConstant p / 2) * cappedMass h *
        ((longCount h : ℝ) ^ (p - 1)) := by
  by_cases heq : ell = longCount h
  · subst ell
    rw [unresolvedMass_longCount]
    have hhalf : 1 ≤ boundaryPropagationConstant p / 2 := by
      unfold boundaryPropagationConstant
      have hA := boundaryErrorConstant_nonneg hp
      have hexp := Real.one_le_exp_iff.mpr hA
      nlinarith
    have hB0 := (cappedMass_pos hh).le
    have hrpow0 : 0 ≤ ((longCount h : ℝ) ^ (p - 1)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhalf hB0) hrpow0]
  · have hellt : ell < longCount h := lt_of_le_of_ne hellr heq
    have hratio := intervalMassRatio_le hp hQ hh hQell hellr (hcut hellt)
    have hB0 := cappedMass_pos hh
    have hD :
        unresolvedMass h ell ≤
          (Real.exp (boundaryErrorConstant p) *
            (((longCount h : ℝ) / (ell : ℝ)) ^ (p - 1))) *
              cappedMass h :=
      (div_le_iff₀ hB0).mp hratio
    have hellR0 : 0 < (ell : ℝ) := by
      have hthetaInv0 : 0 < (lyapunovTheta p)⁻¹ := inv_pos.mpr (lyapunovTheta_pos hp)
      have hQR0 : 0 < (Q : ℝ) := hthetaInv0.trans hQ
      exact_mod_cast (lt_of_lt_of_le (by exact_mod_cast hQR0) hQell)
    have hrR0 : 0 < (longCount h : ℝ) := by
      exact hellR0.trans_le (by exact_mod_cast hellr)
    have hellpow0 : 0 ≤ ((ell : ℝ) ^ (p - 1)) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hD hellpow0
    calc
      unresolvedMass h ell * ((ell : ℝ) ^ (p - 1)) ≤
          ((Real.exp (boundaryErrorConstant p) *
            (((longCount h : ℝ) / (ell : ℝ)) ^ (p - 1))) *
              cappedMass h) * ((ell : ℝ) ^ (p - 1)) := hmul
      _ = Real.exp (boundaryErrorConstant p) * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1)) := by
        rw [Real.div_rpow hrR0.le hellR0.le]
        have hellpowPos : 0 < ((ell : ℝ) ^ (p - 1)) :=
          Real.rpow_pos_of_pos hellR0 _
        field_simp [ne_of_gt hellpowPos]
      _ = (boundaryPropagationConstant p / 2) * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1)) := by
        unfold boundaryPropagationConstant
        ring

/-- Growth under the abstract large-product alternative, corresponding to
`lem:boundary-propagation`.  The matching part of the manuscript is used
only to supply `hcut`; the propagation itself is entirely scalar.

When `k = longCount h`, `hcut` is a condition on the empty interval
`[k+1,r]` and the proof takes the boundary branch directly. -/
theorem boundaryPropagation
    {T : ℕ} {p : ℝ} (hp : 1 < p) {Q : ℕ}
    (_hQ2 : 2 ≤ Q)
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {k : ℕ} (hQk : Q ≤ k) (hkr : k ≤ longCount h)
    (hcut : CutoffConditions p h (k + 1) (longCount h)) :
    unresolvedMass h k * ((k : ℝ) ^ (p - 1)) ≤
      boundaryPropagationConstant p * cappedMass h *
        ((longCount h : ℝ) ^ (p - 1)) := by
  by_cases heq : k = longCount h
  · subst k
    rw [unresolvedMass_longCount]
    have hK := boundaryPropagationConstant_ge_one hp
    have hB0 := (cappedMass_pos hh).le
    have hKB : cappedMass h ≤ boundaryPropagationConstant p * cappedMass h := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hB0
    have hrpow0 : 0 ≤ ((longCount h : ℝ) ^ (p - 1)) := by positivity
    have := mul_le_mul_of_nonneg_right hKB hrpow0
    simpa only [mul_assoc] using this
  · have hkr' : k < longCount h := lt_of_le_of_ne hkr heq
    have hk1r : k + 1 ≤ longCount h := by omega
    have hcore := coreBoundaryPropagation hp hQ hh
      (ell := k + 1) (by omega) hk1r (fun _ ↦ hcut)
    have hk1mem : k + 1 ∈ Finset.Icc (k + 1) (longCount h) :=
      Finset.mem_Icc.mpr ⟨le_rfl, hk1r⟩
    have hnuB := (hcut (k + 1) hk1mem).2.2.1
    have hthetaInv0 : 0 < (lyapunovTheta p)⁻¹ :=
      inv_pos.mpr (lyapunovTheta_pos hp)
    have hk1R0 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hnuRank :
        relativeMassIncrement h (k + 1) < ((k + 1 : ℕ) : ℝ) := by
      have hQcast : (Q : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast (by omega : Q ≤ k + 1)
      exact hnuB.trans (hQ.trans_le hQcast)
    have hratioEq := oneRankMassRatio hh (q := k + 1) (by omega) hk1r
    have hratioEq' :
        unresolvedMass h k / unresolvedMass h (k + 1) =
          1 + relativeMassIncrement h (k + 1) / ((k + 1 : ℕ) : ℝ) := by
      simpa [massRatio] using hratioEq
    have hratioLe :
        unresolvedMass h k / unresolvedMass h (k + 1) ≤ 2 := by
      rw [hratioEq']
      have hfrac :
          relativeMassIncrement h (k + 1) / ((k + 1 : ℕ) : ℝ) < 1 :=
        (div_lt_one hk1R0).2 hnuRank
      linarith
    have hDnext0 := unresolvedMass_pos hh (k + 1)
    have hD : unresolvedMass h k ≤ 2 * unresolvedMass h (k + 1) :=
      (div_le_iff₀ hDnext0).mp hratioLe
    have hkpow :
        ((k : ℝ) ^ (p - 1)) ≤ (((k + 1 : ℕ) : ℝ) ^ (p - 1)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg k)
      · norm_num
      · linarith
    have hkpow0 : 0 ≤ ((k : ℝ) ^ (p - 1)) := by positivity
    have htwod0 : 0 ≤ 2 * unresolvedMass h (k + 1) := by positivity
    have hboundary :
        unresolvedMass h k * ((k : ℝ) ^ (p - 1)) ≤
          (2 * unresolvedMass h (k + 1)) *
            (((k + 1 : ℕ) : ℝ) ^ (p - 1)) :=
      mul_le_mul hD hkpow hkpow0 htwod0
    have hcoreScaled := mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 2)
    calc
      unresolvedMass h k * ((k : ℝ) ^ (p - 1)) ≤
          (2 * unresolvedMass h (k + 1)) *
            (((k + 1 : ℕ) : ℝ) ^ (p - 1)) := hboundary
      _ = 2 *
          (unresolvedMass h (k + 1) *
            (((k + 1 : ℕ) : ℝ) ^ (p - 1))) := by ring
      _ ≤ 2 *
          ((boundaryPropagationConstant p / 2) * cappedMass h *
            ((longCount h : ℝ) ^ (p - 1))) := hcoreScaled
      _ = boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1)) := by ring

end
end RankAnalysis
end GDLowerBound
