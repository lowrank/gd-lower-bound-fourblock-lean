import GDLowerBound.FourBlock.LogBounds

/-!
# Executable rational transcendental certificates

Certificate validity is a Boolean computation over `ℚ`; `native_decide`
can therefore check large generated lists.  The soundness theorem below is
the only bridge to `Real.log`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

def qLogRadius (y : ℚ) : ℚ := (y - 1) / (y + 1)

def qLogSeries (y : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n,
    qLogRadius y ^ (2 * i + 1) / (2 * i + 1)

def qLogSeriesError (y : ℚ) (n : ℕ) : ℚ :=
  |qLogRadius y| ^ (2 * n + 1) / (1 - qLogRadius y ^ 2)

def qLogLower (y : ℚ) (n : ℕ) : ℚ :=
  2 * (qLogSeries y n - qLogSeriesError y n)

def qLogUpper (y : ℚ) (n : ℕ) : ℚ :=
  2 * (qLogSeries y n + qLogSeriesError y n)

theorem coe_qLogRadius (y : ℚ) :
    (qLogRadius y : ℝ) = logRadius (y : ℝ) := by
  norm_num [qLogRadius, logRadius]

theorem coe_qLogSeries (y : ℚ) (n : ℕ) :
    (qLogSeries y n : ℝ) = logSeries (y : ℝ) n := by
  unfold qLogSeries logSeries
  push_cast
  simp only [coe_qLogRadius]

theorem coe_qLogSeriesError (y : ℚ) (n : ℕ) :
    (qLogSeriesError y n : ℝ) = logSeriesError (y : ℝ) n := by
  unfold qLogSeriesError logSeriesError
  push_cast
  rw [coe_qLogRadius]

theorem coe_qLogLower (y : ℚ) (n : ℕ) :
    (qLogLower y n : ℝ) = logLower (y : ℝ) n := by
  unfold qLogLower logLower
  push_cast
  rw [coe_qLogSeries, coe_qLogSeriesError]

theorem coe_qLogUpper (y : ℚ) (n : ℕ) :
    (qLogUpper y n : ℝ) = logUpper (y : ℝ) n := by
  unfold qLogUpper logUpper
  push_cast
  rw [coe_qLogSeries, coe_qLogSeriesError]

structure LogBoundCert where
  y : ℚ
  n : ℕ
  lower : ℚ
  upper : ℚ
deriving Repr, DecidableEq

def LogBoundCert.valid (c : LogBoundCert) : Bool :=
  decide (0 < c.y ∧ c.lower ≤ qLogLower c.y c.n ∧
    qLogUpper c.y c.n ≤ c.upper)

theorem LogBoundCert.sound {c : LogBoundCert} (hc : c.valid = true) :
    (c.lower : ℝ) ≤ Real.log (c.y : ℝ) ∧
      Real.log (c.y : ℝ) ≤ (c.upper : ℝ) := by
  have hvalid : 0 < c.y ∧ c.lower ≤ qLogLower c.y c.n ∧
      qLogUpper c.y c.n ≤ c.upper := of_decide_eq_true hc
  have hy : (0 : ℝ) < c.y := by exact_mod_cast hvalid.1
  have hreal := log_mem_series_bounds hy c.n
  rw [← coe_qLogLower, ← coe_qLogUpper] at hreal
  have hlower : (c.lower : ℝ) ≤ (qLogLower c.y c.n : ℝ) := by
    exact_mod_cast hvalid.2.1
  have hupper : (qLogUpper c.y c.n : ℝ) ≤ (c.upper : ℝ) := by
    exact_mod_cast hvalid.2.2
  exact ⟨hlower.trans hreal.1, hreal.2.trans hupper⟩

structure SqrtBoundCert where
  x : ℚ
  lower : ℚ
  upper : ℚ
deriving Repr, DecidableEq

def SqrtBoundCert.valid (c : SqrtBoundCert) : Bool :=
  decide (0 ≤ c.x ∧ 0 ≤ c.lower ∧ c.lower ^ 2 ≤ c.x ∧
    0 ≤ c.upper ∧ c.x ≤ c.upper ^ 2)

theorem SqrtBoundCert.sound {c : SqrtBoundCert} (hc : c.valid = true) :
    (c.lower : ℝ) ≤ Real.sqrt (c.x : ℝ) ∧
      Real.sqrt (c.x : ℝ) ≤ (c.upper : ℝ) := by
  have hvalid : 0 ≤ c.x ∧ 0 ≤ c.lower ∧ c.lower ^ 2 ≤ c.x ∧
      0 ≤ c.upper ∧ c.x ≤ c.upper ^ 2 := of_decide_eq_true hc
  have hx : (0 : ℝ) ≤ c.x := by exact_mod_cast hvalid.1
  have hlo : (0 : ℝ) ≤ c.lower := by exact_mod_cast hvalid.2.1
  have hhi : (0 : ℝ) ≤ c.upper := by exact_mod_cast hvalid.2.2.2.1
  have hsqrt0 := Real.sqrt_nonneg (c.x : ℝ)
  have hsqrtSq := Real.sq_sqrt hx
  constructor
  · have hsquare : (c.lower : ℝ) ^ 2 ≤ (c.x : ℝ) := by
      exact_mod_cast hvalid.2.2.1
    nlinarith [sq_nonneg ((c.lower : ℝ) - Real.sqrt (c.x : ℝ))]
  · have hsquare : (c.x : ℝ) ≤ (c.upper : ℝ) ^ 2 := by
      exact_mod_cast hvalid.2.2.2.2
    nlinarith [sq_nonneg ((c.upper : ℝ) - Real.sqrt (c.x : ℝ))]

end GDLowerBound.FourBlock
