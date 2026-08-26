import GDLowerBound.FourBlock.TailPowerBounds

/-! # Transfer from rational tail substitutions to the true reference powers -/

namespace GDLowerBound.FourBlock

noncomputable section

def tailTrueProxy (z : ℝ) : ℝ :=
  (tailQ2LowerQ : ℝ) + (tailG82LowerQ : ℝ) +
    (centralAlphaQ : ℝ) * Real.log (tailQmaxQ : ℝ) +
    centralEndpointRaw z +
    (centralLambda2Q : ℝ) *
      Real.log (((tailRatioQ : ℝ) * tailR30 - z) / tailR20)

theorem tailProxy_le_trueProxy {z : ℝ} (harg : 0 < tailArgument z) :
    tailProxy z ≤ tailTrueProxy z := by
  have hd : 0 < (tailR20UpperQ : ℝ) := by norm_num [tailR20UpperQ]
  have he : 0 < tailR20 := by
    unfold tailR20
    exact Real.rpow_pos_of_pos (by norm_num) _
  have he_le : tailR20 ≤ (tailR20UpperQ : ℝ) := tailR20_lt_upper.le
  have hn :
      (tailRatioQ : ℝ) * (tailR30LowerQ : ℝ) - z ≤
        (tailRatioQ : ℝ) * tailR30 - z := by
    have hr := mul_le_mul_of_nonneg_left tailR30Lower_lt.le
      (by norm_num [tailRatioQ] : (0 : ℝ) ≤ tailRatioQ)
    linarith
  have hn0 : 0 < (tailRatioQ : ℝ) * (tailR30LowerQ : ℝ) - z := by
    unfold tailArgument at harg
    exact (div_pos_iff_of_pos_right hd).mp harg
  have hratio : tailArgument z ≤
      ((tailRatioQ : ℝ) * tailR30 - z) / tailR20 := by
    unfold tailArgument
    calc
      ((tailRatioQ : ℝ) * (tailR30LowerQ : ℝ) - z) /
          (tailR20UpperQ : ℝ) ≤
          ((tailRatioQ : ℝ) * tailR30 - z) / (tailR20UpperQ : ℝ) :=
        div_le_div_of_nonneg_right hn hd.le
      _ ≤ ((tailRatioQ : ℝ) * tailR30 - z) / tailR20 :=
        div_le_div_of_nonneg_left (hn0.le.trans hn) he he_le
  have hlog := Real.log_le_log harg hratio
  have hlambda : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  unfold tailProxy tailTrueProxy
  gcongr

theorem certifiedTrueTailProxy {z : ℝ}
    (hzlo : (7982344478949 / 19531250000000 : ℝ) ≤ z)
    (hzhi : z ≤ (119 / 250 : ℝ)) :
    (31 / 1250 : ℝ) < tailTrueProxy z := by
  have hproxy := certifiedTailProxy hzlo hzhi
  have harg : 0 < tailArgument z := by
    unfold tailArgument
    norm_num [tailRatioQ, tailR30LowerQ, tailR20UpperQ] at hzhi ⊢
    linarith
  exact hproxy.trans_le (tailProxy_le_trueProxy harg)

end

end GDLowerBound.FourBlock
