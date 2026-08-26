import GDLowerBound.FourBlock.KernelGradient

/-!
# A supporting plane for the exact four-block matching functional

At fixed scale `z`, the two outside-in edge pairs depend affinely on
`(a,r,s)`.  The exact concavity theorem for the two-variable logarithmic
kernel therefore yields the global supporting plane proved below.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def matchingGradA (z a r s : ℝ) : ℝ :=
  4 * z *
    (kernelGradU (8 * z * a) (8 * z * (1 - s)) -
      kernelGradU (8 * z * (r - a)) (8 * z * (s - r)))

def matchingGradR (z a r s : ℝ) : ℝ :=
  4 * z *
    (kernelGradU (8 * z * (r - a)) (8 * z * (s - r)) -
      kernelGradV (8 * z * (r - a)) (8 * z * (s - r)))

def matchingGradS (z a r s : ℝ) : ℝ :=
  4 * z *
    (-kernelGradV (8 * z * a) (8 * z * (1 - s)) +
      kernelGradV (8 * z * (r - a)) (8 * z * (s - r)))

theorem fourBlockMatching_le_support
    {z a₀ r₀ s₀ a r s : ℝ}
    (hz : 0 < z)
    (ha₀ : 0 < a₀) (h20 : 0 < r₀ - a₀)
    (h30 : 0 < s₀ - r₀) (h40 : 0 < 1 - s₀)
    (ha : 0 < a) (h2 : 0 < r - a)
    (h3 : 0 < s - r) (h4 : 0 < 1 - s) :
    fourBlockMatching z a r s ≤ fourBlockMatching z a₀ r₀ s₀ +
      matchingGradA z a₀ r₀ s₀ * (a - a₀) +
      matchingGradR z a₀ r₀ s₀ * (r - r₀) +
      matchingGradS z a₀ r₀ s₀ * (s - s₀) := by
  let c : ℝ := 8 * z
  have hc : 0 < c := by dsimp only [c]; positivity
  have hu140 : 0 < c * a₀ := mul_pos hc ha₀
  have hv140 : 0 < c * (1 - s₀) := mul_pos hc h40
  have hu14 : 0 < c * a := mul_pos hc ha
  have hv14 : 0 < c * (1 - s) := mul_pos hc h4
  have hu230 : 0 < c * (r₀ - a₀) := mul_pos hc h20
  have hv230 : 0 < c * (s₀ - r₀) := mul_pos hc h30
  have hu23 : 0 < c * (r - a) := mul_pos hc h2
  have hv23 : 0 < c * (s - r) := mul_pos hc h3
  have hout := pairLogKernelClosed_le_support
    hu140 hv140 hu14 hv14
  have hin := pairLogKernelClosed_le_support
    hu230 hv230 hu23 hv23
  rw [pairLogKernelClosed_eq ⟨hu14, hv14⟩,
    pairLogKernelClosed_eq ⟨hu140, hv140⟩] at hout
  rw [pairLogKernelClosed_eq ⟨hu23, hv23⟩,
    pairLogKernelClosed_eq ⟨hu230, hv230⟩] at hin
  dsimp only [c] at hout hin
  unfold fourBlockMatching matchingGradA matchingGradR matchingGradS
  linarith

end

end GDLowerBound.FourBlock
