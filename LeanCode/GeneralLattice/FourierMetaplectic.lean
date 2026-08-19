import LeanCode.GeneralLattice.Metaplectic
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory
open scoped ENNReal SchwartzMap
open FourierTransform

namespace LyubarskiiNes.GeneralLattice

/-- The unweighted complex Gaussian underlying `generalizedH1`. -/
noncomputable def generalizedGaussian (τ : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2)

lemma generalizedH1_eq_mul_gaussian (τ : ℂ) (t : ℝ) :
    generalizedH1 τ t = (t : ℂ) * generalizedGaussian τ t := by
  rfl

lemma norm_generalizedGaussian (τ : ℂ) (t : ℝ) :
    ‖generalizedGaussian τ t‖ =
      Real.exp (-Real.pi * τ.im * t ^ 2) := by
  unfold generalizedGaussian
  rw [Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, pow_two]

private lemma integrable_one_add_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => (1 + t ^ 2) * Real.exp (-b * t ^ 2)) := by
  have hzero := integrable_rpow_mul_exp_neg_mul_sq (b := b) (s := (0 : ℝ)) hb (by norm_num)
  have htwo := integrable_rpow_mul_exp_neg_mul_sq (b := b) (s := (2 : ℝ)) hb (by norm_num)
  have hzero' : Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) := by
    simpa using hzero
  have htwo' : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) := by
    simpa [Real.rpow_natCast] using htwo
  exact (hzero'.add htwo').congr (Filter.Eventually.of_forall fun t => by
    simp only [Pi.add_apply]
    ring)

private lemma integrable_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => |t| * Real.exp (-b * t ^ 2)) := by
  refine (integrable_one_add_sq_mul_exp_neg_mul_sq hb).mono ?_ ?_
  · fun_prop
  · filter_upwards with t
    simp only [Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ 2)]
    have hsquare : |t| ^ 2 = t ^ 2 := sq_abs t
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [sq_nonneg (|t| - 1 / 2)]) (Real.exp_pos _).le

lemma integrable_generalizedGaussian {τ : ℂ} (hτ : 0 < τ.im) :
    Integrable (generalizedGaussian τ) := by
  have hn : Integrable (fun t : ℝ => ‖generalizedGaussian τ t‖) := by
    simpa [norm_generalizedGaussian] using
      (integrable_rpow_mul_exp_neg_mul_sq
        (b := Real.pi * τ.im) (s := (0 : ℝ)) (mul_pos Real.pi_pos hτ) (by norm_num))
  rwa [integrable_norm_iff (by
    exact Continuous.aestronglyMeasurable (by unfold generalizedGaussian; continuity))] at hn

lemma integrable_generalizedH1 {τ : ℂ} (hτ : 0 < τ.im) :
    Integrable (generalizedH1 τ) := by
  have hn : Integrable (fun t : ℝ => ‖generalizedH1 τ t‖) := by
    simpa [norm_generalizedH1, mul_assoc] using
      integrable_abs_mul_exp_neg_mul_sq (mul_pos Real.pi_pos hτ)
  rwa [integrable_norm_iff (by
    exact Continuous.aestronglyMeasurable (by unfold generalizedH1; continuity))] at hn

lemma integrable_id_smul_generalizedGaussian {τ : ℂ} (hτ : 0 < τ.im) :
    Integrable (fun t : ℝ => t • generalizedGaussian τ t) := by
  have heq : (fun t : ℝ => t • generalizedGaussian τ t) = generalizedH1 τ := by
    funext t
    simp [generalizedH1_eq_mul_gaussian]
  rw [heq]
  exact integrable_generalizedH1 hτ

/-- Fourier rotation sends the upper-half-plane parameter to `-1/τ`. -/
noncomputable def fourierTau (τ : ℂ) : ℂ := -τ⁻¹

lemma fourierTau_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (fourierTau τ).im := by
  unfold fourierTau
  rw [Complex.neg_im, Complex.inv_im]
  have hnorm : 0 < Complex.normSq τ := Complex.normSq_pos.mpr (by
    intro h
    rw [h] at hτ
    norm_num at hτ)
  rw [show -(-τ.im / Complex.normSq τ) = τ.im / Complex.normSq τ by ring]
  exact div_pos hτ hnorm

/-- The nonzero scalar appearing in the Fourier transform of a generalized
first-Hermite window. -/
noncomputable def fourierH1Scale (τ : ℂ) : ℂ :=
  let b := -Complex.I * τ
  (1 / b ^ (1 / 2 : ℂ)) / (Complex.I * b)

lemma fourierH1Scale_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    fourierH1Scale τ ≠ 0 := by
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  have hb0 : -Complex.I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0
  unfold fourierH1Scale
  exact div_ne_zero (one_div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hb0)))
    (mul_ne_zero Complex.I_ne_zero hb0)

/-- The ordinary Fourier integral of a generalized first-Hermite window. -/
theorem fourier_generalizedH1_pointwise {τ : ℂ} (hτ : 0 < τ.im) :
    𝓕 (generalizedH1 τ) =
      fun t : ℝ => fourierH1Scale τ * generalizedH1 (fourierTau τ) t := by
  let b : ℂ := -Complex.I * τ
  have hb : 0 < b.re := by
    simp [b, Complex.mul_re]
    exact hτ
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  have hb0 : b ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0
  have hgauss :
      𝓕 (generalizedGaussian τ) = fun t : ℝ =>
        1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (t : ℂ) ^ 2) := by
    change 𝓕 (fun x : ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2)) = _
    convert (fourier_gaussian_pi (b := b) hb) using 1
    funext x
    congr 1
    dsimp [b]
    ring
  have hderiv := Real.deriv_fourier
    (integrable_generalizedGaussian hτ)
    (integrable_id_smul_generalizedGaussian hτ)
  rw [hgauss] at hderiv
  have hinput :
      (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
          generalizedGaussian τ x) =
        (-2 * (Real.pi : ℂ) * Complex.I) • generalizedH1 τ := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [generalizedH1_eq_mul_gaussian]
    ring
  rw [hinput] at hderiv
  have hfourier_smul :
      𝓕 ((-2 * (Real.pi : ℂ) * Complex.I) • generalizedH1 τ) =
        (-2 * (Real.pi : ℂ) * Complex.I) • 𝓕 (generalizedH1 τ) := by
    funext w
    simp only [Pi.smul_apply]
    rw [Real.fourier_eq, Real.fourier_eq]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.smul_apply, Circle.smul_def]
    ring
  rw [hfourier_smul] at hderiv
  funext t
  have hd :
      deriv (fun u : ℝ =>
          1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (u : ℂ) ^ 2)) t =
        (1 / b ^ (1 / 2 : ℂ)) *
          (2 * (-Real.pi / b) * (t : ℂ)) *
          Complex.exp (-Real.pi / b * (t : ℂ) ^ 2) := by
    have hc := (((hasDerivAt_id (t : ℂ)).pow 2).const_mul
      (-Real.pi / b)).cexp.const_mul (1 / b ^ (1 / 2 : ℂ))
    have hr := hc.comp_ofReal
    have hrd := hr.deriv
    simp only [Pi.pow_apply, id_eq, one_div, Nat.cast_ofNat, pow_one, mul_one] at hrd
    convert hrd using 1 <;> ring
  have ht := congrFun hderiv t
  rw [hd] at ht
  have hexp :
      (Real.pi : ℂ) * Complex.I * fourierTau τ * (t : ℂ) ^ 2 =
        -Real.pi / b * (t : ℂ) ^ 2 := by
    unfold fourierTau
    dsimp [b]
    field_simp [hτ0]
    simp [pow_two, Complex.I_mul_I]
  rw [generalizedH1, hexp]
  have hscale : fourierH1Scale τ =
      (1 / b ^ (1 / 2 : ℂ)) / (Complex.I * b) := by
    simp [fourierH1Scale, b]
  rw [hscale]
  let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  apply (mul_left_cancel₀ hc0)
  have ht' : c * (𝓕 (generalizedH1 τ)) t =
      (1 / b ^ (1 / 2 : ℂ)) *
        (2 * (-Real.pi / b) * (t : ℂ)) *
        Complex.exp (-Real.pi / b * (t : ℂ) ^ 2) := by
    simpa [c, Pi.smul_apply, smul_eq_mul] using ht.symm
  rw [ht']
  dsimp [c]
  field_simp [hb0, Real.pi_ne_zero]

/-- Compatibility of the `L¹` Fourier integral and Mathlib's unitary `L²`
Fourier transform, in the form needed below. -/
private theorem fourierLp_eq_toLp_of_integrable
    {f g : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hfg : 𝓕 f = g) :
    𝓕 (hf2.toLp : Lp ℂ 2 (volume : Measure ℝ)) = hg2.toLp := by
  let T := MeasureTheory.Lp.toTemperedDistributionCLM ℂ
    (volume : Measure ℝ) 2
  have hT : Function.Injective T :=
    LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  apply hT
  change MeasureTheory.Lp.toTemperedDistribution
      (𝓕 (hf2.toLp : Lp ℂ 2 (volume : Measure ℝ))) =
    MeasureTheory.Lp.toTemperedDistribution hg2.toLp
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  ext φ
  simp only [TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  have hleft :
      (∫ x : ℝ, (𝓕 φ) x • (hf2.toLp : ℝ → ℂ) x) =
        ∫ x : ℝ, (𝓕 φ) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hright :
      (∫ x : ℝ, φ x • (hg2.toLp : ℝ → ℂ) x) =
        ∫ x : ℝ, φ x • g x := by
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx]
  rw [hleft, hright, ← hfg]
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner φ.integrable hf1
  have hleftFourier (x : ℝ) :
      (𝓕 φ) x = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (φ : ℝ → ℂ) x := by
    rw [SchwartzMap.fourier_coe]
    rfl
  have hflipFourier (x : ℝ) :
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip f x = 𝓕 f x := by
    rw [VectorFourier.fourierIntegral, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with v
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    rw [real_inner_comm]
  calc
    (∫ x : ℝ, (𝓕 φ) x • f x) =
        ∫ x : ℝ, (VectorFourier.fourierIntegral 𝐞 volume
          (innerₗ ℝ) (φ : ℝ → ℂ) x) • f x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hleftFourier]
    _ = ∫ x : ℝ, φ x •
        VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip f x := hswap
    _ = ∫ x : ℝ, φ x • 𝓕 f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hflipFourier]

/-- Mathlib's unitary `L²` Fourier transform has the same explicit action on
the generalized first-Hermite window. -/
theorem fourierLinearIsometryEquiv_generalizedH1
    (τ : ℂ) (hτ : 0 < τ.im) :
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (generalizedH1Lp τ hτ) =
      fourierH1Scale τ •
        generalizedH1Lp (fourierTau τ) (fourierTau_im_pos hτ) := by
  let g : ℝ → ℂ := fun t =>
    fourierH1Scale τ * generalizedH1 (fourierTau τ) t
  have hg2 : MemLp g 2 (volume : Measure ℝ) := by
    exact (memLp_generalizedH1 (fourierTau_im_pos hτ)).const_mul (fourierH1Scale τ)
  have hL2 := fourierLp_eq_toLp_of_integrable
    (integrable_generalizedH1 hτ) (memLp_generalizedH1 hτ) hg2
    (fourier_generalizedH1_pointwise hτ)
  change 𝓕 (generalizedH1Lp τ hτ) = _
  calc
    𝓕 (generalizedH1Lp τ hτ) = hg2.toLp := hL2
    _ = fourierH1Scale τ •
        generalizedH1Lp (fourierTau τ) (fourierTau_im_pos hτ) := by
      apply Lp.ext
      filter_upwards [hg2.coeFn_toLp,
        (memLp_generalizedH1 (fourierTau_im_pos hτ)).coeFn_toLp,
        Lp.coeFn_smul (fourierH1Scale τ)
          (generalizedH1Lp (fourierTau τ) (fourierTau_im_pos hτ))] with
          t hg ht hsmul
      rw [hg, hsmul, Pi.smul_apply]
      unfold generalizedH1Lp
      rw [ht]
      rfl

/-- The harmless phase produced when Fourier transform interchanges a time
shift by `x` and a frequency shift by `ω`. -/
noncomputable def fourierAtomPhase (x ω : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ))

@[simp] lemma norm_fourierAtomPhase (x ω : ℝ) :
    ‖fourierAtomPhase x ω‖ = 1 := by
  unfold fourierAtomPhase
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ) =
        ((2 * Real.pi * x * ω : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

lemma fourierAtomPhase_ne_zero (x ω : ℝ) : fourierAtomPhase x ω ≠ 0 :=
  by
    unfold fourierAtomPhase
    exact Complex.exp_ne_zero _

private lemma integrable_generalizedH1_shift_modulation
    {τ : ℂ} (hτ : 0 < τ.im) (x ω : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - x)) := by
  have hshift : Integrable (fun t : ℝ => generalizedH1 τ (t - x)) := by
    have hmp := MeasureTheory.measurePreserving_sub_right
      (volume : Measure ℝ) x
    exact (hmp.integrable_comp (integrable_generalizedH1 hτ).aestronglyMeasurable).2
      (integrable_generalizedH1 hτ)
  have hn : Integrable (fun t : ℝ =>
      ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - x)‖) := by
    exact hshift.norm.congr (Filter.Eventually.of_forall fun t => by
      change ‖generalizedH1 τ (t - x)‖ =
        ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
          generalizedH1 τ (t - x)‖
      rw [norm_mul]
      have harg :
          2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ) =
            ((2 * Real.pi * ω * t : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.norm_exp_ofReal_mul_I, one_mul])
  rwa [integrable_norm_iff (by
    exact Continuous.aestronglyMeasurable (by
      unfold generalizedH1
      fun_prop))] at hn

/-- Ordinary Fourier covariance for one translated and modulated generalized
first-Hermite atom. -/
private theorem fourier_generalizedH1_shift_modulation
    {τ : ℂ} (hτ : 0 < τ.im) (x ω : ℝ) :
    𝓕 (fun t : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - x)) =
      fun ξ : ℝ =>
        (fourierAtomPhase x ω * fourierH1Scale τ) *
          (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) * (ξ : ℂ)) *
            generalizedH1 (fourierTau τ) (ξ - ω)) := by
  funext ξ
  rw [Real.fourier_eq']
  simp only [smul_eq_mul, Real.inner_apply]
  let F : ℝ → ℂ := fun t =>
    Complex.exp ((↑(-2 * Real.pi * (t * ξ)) : ℂ) * Complex.I) *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - x))
  change (∫ t : ℝ, F t) = _
  rw [← MeasureTheory.integral_add_right_eq_self F x]
  have hpoint (t : ℝ) :
      F (t + x) = fourierAtomPhase x ω *
        (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) * (ξ : ℂ)) *
          (Complex.exp ((↑(-2 * Real.pi * (t * (ξ - ω))) : ℂ) * Complex.I) *
            generalizedH1 τ t)) := by
    unfold F fourierAtomPhase
    rw [show t + x - x = t by ring]
    have harg :
        ((↑(-2 * Real.pi * ((t + x) * ξ)) : ℂ) * Complex.I) +
            (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * ((t + x : ℝ) : ℂ)) =
          (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ)) +
            (2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) * (ξ : ℂ)) +
            ((↑(-2 * Real.pi * (t * (ξ - ω))) : ℂ) * Complex.I) := by
      push_cast
      ring
    calc
      Complex.exp ((↑(-2 * Real.pi * ((t + x) * ξ)) : ℂ) * Complex.I) *
            (Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * ((t + x : ℝ) : ℂ)) *
              generalizedH1 τ t) =
          Complex.exp
              (((↑(-2 * Real.pi * ((t + x) * ξ)) : ℂ) * Complex.I) +
                (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * ((t + x : ℝ) : ℂ))) *
            generalizedH1 τ t := by rw [Complex.exp_add]; ring
      _ = Complex.exp
              ((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ)) +
                (2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) * (ξ : ℂ)) +
                ((↑(-2 * Real.pi * (t * (ξ - ω))) : ℂ) * Complex.I)) *
            generalizedH1 τ t := by rw [harg]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (ω : ℂ)) *
            (Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) * (ξ : ℂ)) *
              (Complex.exp ((↑(-2 * Real.pi * (t * (ξ - ω))) : ℂ) * Complex.I) *
                generalizedH1 τ t)) := by
          rw [Complex.exp_add, Complex.exp_add]
          ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_const_mul]
  have hwindow := congrFun (fourier_generalizedH1_pointwise hτ) (ξ - ω)
  rw [Real.fourier_eq'] at hwindow
  simp only [smul_eq_mul, Real.inner_apply] at hwindow
  rw [hwindow]
  ring

/-- The quarter rotation which sends `(x,ω)` to `(ω,-x)`. -/
noncomputable def fourierRotationMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix 0 1

@[simp] lemma latticeTime_fourierRotationMatrix_mul
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeTime (fourierRotationMatrix * M) m n = latticeFrequency M m n := by
  simp [fourierRotationMatrix, rotationMatrix, latticeTime, latticeFrequency,
    Matrix.mul_apply]

@[simp] lemma latticeFrequency_fourierRotationMatrix_mul
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeFrequency (fourierRotationMatrix * M) m n = -latticeTime M m n := by
  simp [fourierRotationMatrix, rotationMatrix, latticeTime, latticeFrequency,
    Matrix.mul_apply]
  ring

theorem fourier_generalizedH1LatticeElement_pointwise
    {τ : ℂ} (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    𝓕 (generalizedH1LatticeElement τ M m n) = fun ξ : ℝ =>
      (fourierAtomPhase (latticeTime M m n) (latticeFrequency M m n) *
          fourierH1Scale τ) *
        generalizedH1LatticeElement (fourierTau τ)
          (fourierRotationMatrix * M) m n ξ := by
  change 𝓕 (fun t : ℝ =>
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            (latticeFrequency M m n : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - latticeTime M m n)) = _
  simpa only [generalizedH1LatticeElement,
    latticeTime_fourierRotationMatrix_mul,
    latticeFrequency_fourierRotationMatrix_mul] using
      (fourier_generalizedH1_shift_modulation hτ
        (latticeTime M m n) (latticeFrequency M m n))

/-- Unitary `L²` Fourier covariance for every generalized Hermite lattice
atom. -/
theorem fourierLinearIsometryEquiv_generalizedH1LatticeElementLp
    {τ : ℂ} (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (generalizedH1LatticeElementLp τ hτ M m n) =
      (fourierAtomPhase (latticeTime M m n) (latticeFrequency M m n) *
          fourierH1Scale τ) •
        generalizedH1LatticeElementLp (fourierTau τ) (fourierTau_im_pos hτ)
          (fourierRotationMatrix * M) m n := by
  let c : ℂ := fourierAtomPhase (latticeTime M m n) (latticeFrequency M m n) *
    fourierH1Scale τ
  let newAtom : ℝ → ℂ := generalizedH1LatticeElement (fourierTau τ)
    (fourierRotationMatrix * M) m n
  let g : ℝ → ℂ := fun t => c * newAtom t
  have hg2 : MemLp g 2 (volume : Measure ℝ) := by
    exact (memLp_generalizedH1LatticeElement (fourierTau_im_pos hτ)
      (fourierRotationMatrix * M) m n).const_mul c
  have hold1 : Integrable (generalizedH1LatticeElement τ M m n) := by
    change Integrable (fun t : ℝ =>
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            (latticeFrequency M m n : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - latticeTime M m n))
    exact integrable_generalizedH1_shift_modulation hτ
      (latticeTime M m n) (latticeFrequency M m n)
  have hL2 := fourierLp_eq_toLp_of_integrable hold1
    (memLp_generalizedH1LatticeElement hτ M m n) hg2
    (fourier_generalizedH1LatticeElement_pointwise hτ M m n)
  change 𝓕 (generalizedH1LatticeElementLp τ hτ M m n) = _
  change 𝓕 (generalizedH1LatticeElementLp τ hτ M m n) =
    c • generalizedH1LatticeElementLp (fourierTau τ) (fourierTau_im_pos hτ)
      (fourierRotationMatrix * M) m n
  calc
    𝓕 (generalizedH1LatticeElementLp τ hτ M m n) = hg2.toLp := hL2
    _ = c • generalizedH1LatticeElementLp (fourierTau τ) (fourierTau_im_pos hτ)
        (fourierRotationMatrix * M) m n := by
      apply Lp.ext
      filter_upwards [hg2.coeFn_toLp,
        (memLp_generalizedH1LatticeElement (fourierTau_im_pos hτ)
          (fourierRotationMatrix * M) m n).coeFn_toLp,
        Lp.coeFn_smul c
          (generalizedH1LatticeElementLp (fourierTau τ) (fourierTau_im_pos hτ)
            (fourierRotationMatrix * M) m n)] with t hg ht hsmul
      rw [hg, hsmul, Pi.smul_apply]
      dsimp [g, newAtom]
      unfold generalizedH1LatticeElementLp
      rw [ht]

/-- Metaplectic covariance for the Fourier/quarter-rotation generator. -/
theorem isGeneralizedGaborFrameForLattice_fourier_iff
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice (fourierTau τ) (fourierTau_im_pos hτ)
        (fourierRotationMatrix * M) ↔
      IsGeneralizedGaborFrameForLattice τ hτ M := by
  rw [isGeneralizedGaborFrameForLattice_iff_isFrameFamily,
    isGeneralizedGaborFrameForLattice_iff_isFrameFamily]
  let U := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
  let oldFamily := generalizedH1LatticeElementLp τ hτ M
  let newFamily := generalizedH1LatticeElementLp (fourierTau τ)
    (fourierTau_im_pos hτ) (fourierRotationMatrix * M)
  have hcov : ∀ m n, U (oldFamily m n) =
      fourierAtomPhase (latticeTime M m n) (latticeFrequency M m n) •
        (fourierH1Scale τ • newFamily m n) := by
    intro m n
    rw [← mul_smul]
    exact fourierLinearIsometryEquiv_generalizedH1LatticeElementLp hτ M m n
  have hcongr : IsFrameFamily (fun m n => U (oldFamily m n)) ↔
      IsFrameFamily (fun m n => fourierH1Scale τ • newFamily m n) := by
    apply isFrameFamily_congr
    intro f m n
    rw [hcov]
    simp [norm_fourierAtomPhase]
  calc
    IsFrameFamily newFamily ↔
        IsFrameFamily (fun m n => fourierH1Scale τ • newFamily m n) :=
      (isFrameFamily_smul newFamily (fourierH1Scale τ)
        (fourierH1Scale_ne_zero hτ)).symm
    _ ↔ IsFrameFamily (fun m n => U (oldFamily m n)) := hcongr.symm
    _ ↔ IsFrameFamily oldFamily := isFrameFamily_linearIsometryEquiv U oldFamily

end LyubarskiiNes.GeneralLattice
