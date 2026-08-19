import Mathlib

open MeasureTheory

namespace LyubarskiiNes

/-- Definition of an element of the separable Hermite Gabor system. -/
noncomputable def h1_element (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * β * n * x) * (x - (α * m)) * Complex.exp (- Real.pi * ((x - (α * m))^2))

private theorem h1_element_norm_sq (α β : ℝ) (m n : ℤ) (x : ℝ) :
    ‖h1_element α β m n x‖ ^ 2 =
      (x - α * m) ^ (2 : ℕ) * Real.exp (-(2 * Real.pi) * (x - α * m) ^ 2) := by
  have hmod : ‖Complex.exp (2 * Real.pi * Complex.I * β * n * x)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * β * n * x).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, mul_left_comm, mul_comm]
    rw [hre]
    simp
  have hsub : (↑x - ↑α * ↑m : ℂ) = ((x - α * m : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_mul]
  have hsq : (↑x - ↑α * ↑m : ℂ) ^ 2 = (((x - α * m) ^ 2 : ℝ) : ℂ) := by
    norm_num [pow_two, Complex.ofReal_mul]
  have hreal : ‖(↑x - ↑α * ↑m : ℂ)‖ = |x - α * m| := by
    rw [hsub]
    exact RCLike.norm_ofReal (K := ℂ) (x - α * m)
  have hsq_re : ((↑x - ↑α * ↑m : ℂ) ^ 2).re = (x - α * m) ^ 2 := by
    calc
      ((↑x - ↑α * ↑m : ℂ) ^ 2).re = (((x - α * m) ^ 2 : ℝ) : ℂ).re := by
        exact congrArg Complex.re hsq
      _ = (x - α * m) ^ 2 := by
        exact Complex.ofReal_re ((x - α * m) ^ 2)
  have hgauss :
      ‖Complex.exp (-↑Real.pi * (↑x - ↑α * ↑m : ℂ) ^ 2)‖ =
        Real.exp (-Real.pi * (x - α * m) ^ 2) := by
    rw [Complex.norm_exp]
    have hre : ((-(Real.pi : ℂ) * (↑x - ↑α * ↑m : ℂ) ^ 2).re) =
        -Real.pi * (x - α * m) ^ 2 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hsq_re]
    rw [hre]
  unfold h1_element
  rw [Complex.norm_mul, Complex.norm_mul, hmod, hreal, hgauss]
  simp only [one_mul]
  rw [mul_pow, sq_abs]
  rw [show Real.exp (-Real.pi * (x - α * ↑m) ^ 2) ^ 2 =
      Real.exp (-Real.pi * (x - α * ↑m) ^ 2) *
        Real.exp (-Real.pi * (x - α * ↑m) ^ 2) by ring]
  rw [← Real.exp_add]
  ring_nf

private theorem integrable_gaussian_sq_shift (c : ℝ) :
    Integrable (fun x : ℝ => (x - c) ^ (2 : ℕ) *
      Real.exp (-(2 * Real.pi) * (x - c) ^ 2)) (volume : Measure ℝ) := by
  let g : ℝ → ℝ := fun y => y ^ (2 : ℕ) * Real.exp (-(2 * Real.pi) * y ^ 2)
  have hg : Integrable g (volume : Measure ℝ) := by
    simpa [g, Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := 2 * Real.pi)
        (s := (2 : ℝ)) (by positivity) (by norm_num : (-1 : ℝ) < 2))
  have htrans : Integrable (g ∘ fun x : ℝ => x - c) (volume : Measure ℝ) :=
    ((MeasureTheory.measurePreserving_sub_right (volume : Measure ℝ) c).integrable_comp
      hg.aestronglyMeasurable).2 hg
  simpa [g, Function.comp_def] using htrans

/-- L²-membership of the first Hermite Gabor atoms. -/
theorem memLp_h1 (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) :
    MemLp (h1_element α β m n) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (h1_element α β m n) (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    unfold h1_element
    continuity
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  exact (integrable_gaussian_sq_shift (α * m)).congr
    (Filter.Eventually.of_forall fun x => (h1_element_norm_sq α β m n x).symm)

/-- h1 α β m n as the actual element of L²(ℝ). -/
noncomputable def h1_element_Lp (α β : ℝ) (m n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_h1 α β m n).toLp

/-- Property that the separable Gabor system `G(h₁, α, β)` is a frame. -/
def IsGaborFrame (α : ℝ) (β : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
    A * ‖x‖ ^ 2 ≤ ∑' (m : ℤ) (n : ℤ), ‖inner ℂ x (h1_element_Lp α β m n)‖ ^ 2
    ∧ ∑' (m : ℤ) (n : ℤ), ‖inner ℂ x (h1_element_Lp α β m n)‖ ^ 2 ≤ B * ‖x‖ ^ 2

/-- The paper's theta function, backed by Mathlib's `jacobiTheta₂`. -/
noncomputable abbrev theta := jacobiTheta₂

end LyubarskiiNes
