import LeanCode.RationalDensity.RationalPositive.RankBounds

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- The transform-level first-Hermite Gaussian-Zak formula follows from the
`h₀` Poisson/theta formula and the termwise derivative bridge for the Zak
series. -/
lemma gaussianZakH1_formula_of_h0_and_deriv_bridge
    (h0formula : ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH0C x ω = gaussianZakH0ClosedForm γ ω x)
    (hderivBridge : ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH1C x ω =
        (-(2 * (Real.pi : ℂ)))⁻¹ *
          deriv (fun y : ℝ => Zak.zakTransform γ gaussianH0C y ω) x) :
    ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH1C x ω = gaussianZakH1ClosedForm γ ω x := by
  intro γ hγ x ω
  rw [hderivBridge γ hγ x ω]
  have hfun : (fun y : ℝ => Zak.zakTransform γ gaussianH0C y ω) =
      fun y : ℝ => gaussianZakH0ClosedForm γ ω y := by
    funext y
    exact h0formula γ hγ y ω
  rw [hfun]
  exact (Zgamma_h1_eq γ hγ ω x).symm

/-- For a positive real scale, the complex square-root branch used in Mathlib's
Gaussian Poisson theorem sends `(γ : ℂ)^2` back to `γ`. -/
lemma cpow_sq_half_eq_of_pos_real (γ : ℝ) (hγ : 0 < γ) :
    ((γ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (γ : ℂ) := by
  have hhalf : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [hhalf]
  change Complex.sqrt ((γ : ℂ) ^ 2) = (γ : ℂ)
  have hsq : ((γ : ℂ) ^ 2) = ((γ ^ 2 : ℝ) : ℂ) := by
    norm_num [pow_two, Complex.ofReal_mul]
  rw [hsq]
  rw [Complex.sqrt_of_nonneg]
  · exact_mod_cast (by
      show Real.sqrt (((γ ^ 2 : ℝ) : ℂ).re) = γ
      rw [Complex.ofReal_re]
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_pos hγ)
  · exact_mod_cast sq_nonneg γ

/-- Each Poisson-side summand is the common Gaussian/phase prefactor times a
Mathlib `jacobiTheta₂` summand at the negative theta argument. -/
lemma gaussianZakH0_poisson_term_eq_theta_term
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) (n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) / ((γ : ℂ) ^ 2) *
      ((n : ℂ) +
        Complex.I * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ))) ^ 2) =
      Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
          (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
        jacobiTheta₂_term n (-(gaussianZakThetaArg γ ω x)) (gaussianZakTau γ) := by
  unfold jacobiTheta₂_term gaussianZakThetaArg gaussianZakTau
  rw [← Complex.exp_add]
  congr 1
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hγ
  field_simp [hγc]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The Poisson-side sum is the common Gaussian/phase prefactor times the
theta function at the negative theta argument. -/
lemma gaussianZakH0_poisson_sum_eq_theta
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    (∑' n : ℤ,
      Complex.exp (-(Real.pi : ℂ) / ((γ : ℂ) ^ 2) *
        ((n : ℂ) +
          Complex.I * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ))) ^ 2)) =
      Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
          (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
        jacobiTheta₂ (-(gaussianZakThetaArg γ ω x)) (gaussianZakTau γ) := by
  calc
    (∑' n : ℤ,
      Complex.exp (-(Real.pi : ℂ) / ((γ : ℂ) ^ 2) *
        ((n : ℂ) +
          Complex.I * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ))) ^ 2))
        = ∑' n : ℤ,
          Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
              (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
              2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
            jacobiTheta₂_term n (-(gaussianZakThetaArg γ ω x)) (gaussianZakTau γ) := by
          apply tsum_congr
          intro n
          exact gaussianZakH0_poisson_term_eq_theta_term γ hγ x ω n
    _ = Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
          (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
        (∑' n : ℤ, jacobiTheta₂_term n (-(gaussianZakThetaArg γ ω x)) (gaussianZakTau γ)) := by
          rw [tsum_mul_left]
    _ = Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
          (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
        jacobiTheta₂ (-(gaussianZakThetaArg γ ω x)) (gaussianZakTau γ) := by
          rfl

/-- Remaining algebraic identification after applying Gaussian Poisson summation
to the quadratic form of the `h₀` Zak series. -/
theorem gaussianZakH0_poisson_rhs_eq_closedForm
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
      (1 / ((γ : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        (∑' n : ℤ,
          Complex.exp (-(Real.pi : ℂ) / ((γ : ℂ) ^ 2) *
            ((n : ℂ) +
              Complex.I * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ))) ^ 2))) =
      gaussianZakH0ClosedForm γ ω x := by
  rw [gaussianZakH0_poisson_sum_eq_theta γ hγ x ω]
  rw [cpow_sq_half_eq_of_pos_real γ hγ]
  rw [jacobiTheta₂_neg_left]
  unfold gaussianZakH0ClosedForm gaussianZakPhase gaussianZakPhaseSlope
    gaussianZakThetaArg gaussianZakTau
  simp only [LyubarskiiNes.theta]
  have hexp :
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
          Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
            (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) =
        Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        (1 / (γ : ℂ) *
          (Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
            (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
            jacobiTheta₂ ((γ : ℂ)⁻¹ * (x : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
              (Complex.I / (γ : ℂ) ^ 2)))
        = (1 / (γ : ℂ)) *
          (Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
            Complex.exp ((Real.pi : ℂ) * (x : ℂ) ^ 2 -
              (Real.pi : ℂ) * (ω : ℂ) ^ 2 +
              2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ))) *
            jacobiTheta₂ ((γ : ℂ)⁻¹ * (x : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
              (Complex.I / (γ : ℂ) ^ 2) := by
          ring
    _ = (1 / (γ : ℂ)) *
          (Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ))) *
            jacobiTheta₂ ((γ : ℂ)⁻¹ * (x : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
              (Complex.I / (γ : ℂ) ^ 2) := by
          rw [hexp]
    _ = (γ : ℂ)⁻¹ * Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
            jacobiTheta₂ ((γ : ℂ)⁻¹ * (x : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
              (Complex.I / (γ : ℂ) ^ 2)) := by
          ring

/-- Rewrites one Gaussian `h₀` Zak summand as the quadratic exponential to
which Mathlib's Gaussian Poisson summation theorem applies. -/
lemma gaussianZakH0_zak_summand_eq_quadratic
    (γ x ω : ℝ) (k : ℤ) :
    gaussianH0C (x - γ * (k : ℝ)) * Zak.zakPhase γ k ω =
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (γ : ℂ) ^ 2 * (k : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) *
            (k : ℂ)) := by
  unfold gaussianH0C gaussianH0 Zak.zakPhase
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_pow]
  ring_nf

/-- Rewrites the Gaussian `h₀` Zak transform as the quadratic exponential
series used in `Complex.tsum_exp_neg_quadratic`. -/
lemma gaussianZakH0_zakTransform_eq_quadratic_tsum
    (γ x ω : ℝ) :
    Zak.zakTransform γ gaussianH0C x ω =
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        (∑' k : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (γ : ℂ) ^ 2 * (k : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) *
              ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) * (k : ℂ))) := by
  rw [Zak.zakTransform_eq_tsum_zakPhase]
  calc
    (∑' k : ℤ, gaussianH0C (x - γ * (k : ℝ)) * Zak.zakPhase γ k ω)
        = ∑' k : ℤ,
            Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
              Complex.exp (-(Real.pi : ℂ) * (γ : ℂ) ^ 2 * (k : ℂ) ^ 2 +
                2 * (Real.pi : ℂ) *
                  ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) *
                    (k : ℂ)) := by
          apply tsum_congr
          intro k
          exact gaussianZakH0_zak_summand_eq_quadratic γ x ω k
    _ = Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        (∑' k : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (γ : ℂ) ^ 2 * (k : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) *
              ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) * (k : ℂ))) := by
          rw [tsum_mul_left]

/-- Poisson summation applied to the quadratic series obtained from the
Gaussian `h₀` Zak transform. -/
lemma gaussianZakH0_quadratic_tsum_poisson
    (γ x ω : ℝ) (hγ : 0 < γ) :
    (∑' k : ℤ,
      Complex.exp (-(Real.pi : ℂ) * (γ : ℂ) ^ 2 * (k : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) *
          ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) * (k : ℂ))) =
      1 / ((γ : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        (∑' n : ℤ,
          Complex.exp (-(Real.pi : ℂ) / ((γ : ℂ) ^ 2) *
            ((n : ℂ) +
              Complex.I * ((γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ))) ^ 2)) := by
  have hre : ((γ : ℂ) ^ 2).re = γ ^ 2 := by
    norm_num [pow_two, Complex.ofReal_mul]
  have ha : 0 < ((γ : ℂ) ^ 2).re := by
    rw [hre]
    exact sq_pos_of_pos hγ
  simpa using Complex.tsum_exp_neg_quadratic (a := (γ : ℂ) ^ 2)
    (b := (γ : ℂ) * (x : ℂ) + Complex.I * (γ : ℂ) * (ω : ℂ)) ha

/-- Scalar Gaussian Poisson/theta identity for the `h₀` Zak transform. -/
theorem gaussianZakH0_transform_formula
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    Zak.zakTransform γ gaussianH0C x ω = gaussianZakH0ClosedForm γ ω x := by
  rw [gaussianZakH0_zakTransform_eq_quadratic_tsum γ x ω]
  rw [gaussianZakH0_quadratic_tsum_poisson γ x ω hγ]
  exact gaussianZakH0_poisson_rhs_eq_closedForm γ hγ x ω

/-- The Zak transform commutes with multiplying the window by a scalar. -/
lemma zakTransform_const_mul (γ : ℝ) (c : ℂ) (f : ℝ → ℂ) (x ω : ℝ) :
    Zak.zakTransform γ (fun t : ℝ => c * f t) x ω =
      c * Zak.zakTransform γ f x ω := by
  unfold Zak.zakTransform
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-- Exact norm of a differentiated Gaussian Zak summand.  This isolates the
polynomial-times-Gaussian expression that the local majorant must dominate. -/
lemma norm_deriv_gaussianH0C_mul_zakPhase
    (γ : ℝ) (k : ℤ) (ω t : ℝ) :
    ‖deriv gaussianH0C t * Zak.zakPhase γ k ω‖ =
      (2 * Real.pi) * |t| * Real.exp (-Real.pi * t ^ 2) := by
  rw [norm_mul, Zak.norm_zakPhase, mul_one]
  rw [deriv_gaussianH0C, norm_mul, norm_gaussianH1C]
  have hnorm : ‖((-(2 * Real.pi) : ℝ) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [hnorm]
  ring

/-- Gaussian samples are dominated by the standard theta summability majorant. -/
lemma gaussianH0C_sample_norm_le_theta_bound
    (γ : ℝ) (hγ : 0 < γ) (x : ℝ) (n : ℤ) :
    ‖gaussianH0C (x - γ * (n : ℝ))‖ ≤
      Real.exp (-Real.pi * (γ ^ 2 * (n : ℝ) ^ 2 - 2 * (γ * |x|) * |(n : ℝ)|)) := by
  rw [norm_gaussianH0C]
  apply Real.exp_le_exp.mpr
  have hquad : γ ^ 2 * (n : ℝ) ^ 2 - 2 * (γ * |x|) * |(n : ℝ)| ≤
      (x - γ * (n : ℝ)) ^ 2 := by
    have hnx : (n : ℝ) * x ≤ |(n : ℝ)| * |x| := by
      calc
        (n : ℝ) * x ≤ |(n : ℝ) * x| := le_abs_self _
        _ = |(n : ℝ)| * |x| := abs_mul _ _
    have hmul : γ * ((n : ℝ) * x) ≤ γ * (|(n : ℝ)| * |x|) :=
      mul_le_mul_of_nonneg_left hnx hγ.le
    nlinarith [sq_nonneg x]
  nlinarith [Real.pi_pos]

/-- Summability of the Gaussian sample norms at a positive Zak scale. -/
lemma summable_norm_gaussianH0C_samples_of_pos
    (γ : ℝ) (hγ : 0 < γ) (x : ℝ) :
    Summable fun k : ℤ => ‖gaussianH0C (x - γ * (k : ℝ))‖ := by
  have hT : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have htheta := summable_pow_mul_jacobiTheta₂_term_bound (γ * |x|) hT 0
  have htheta0 : Summable fun k : ℤ =>
      Real.exp (-Real.pi * (γ ^ 2 * (k : ℝ) ^ 2 - 2 * (γ * |x|) * |(k : ℝ)|)) := by
    simpa using htheta
  refine htheta0.of_norm_bounded ?_
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact gaussianH0C_sample_norm_le_theta_bound γ hγ x k

/-- Summability of the base Gaussian `h₀` Zak phase series at positive scale. -/
lemma summable_gaussianH0C_zakPhase_of_pos
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    Summable fun k : ℤ =>
      gaussianH0C (x - γ * (k : ℝ)) * Zak.zakPhase γ k ω := by
  exact Zak.summable_zakTransform_terms_of_norm_summable
    (ρ := γ) (f := gaussianH0C) (x := x) (ω := ω)
    (summable_norm_gaussianH0C_samples_of_pos γ hγ x)

/-- Points in the unit neighborhood of `x` have absolute value bounded by
`|x| + 1`. -/
lemma abs_le_abs_add_one_of_mem_Ioo {x y : ℝ}
    (hy : y ∈ Set.Ioo (x - 1) (x + 1)) :
    |y| ≤ |x| + 1 := by
  have hdist : |y - x| < 1 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hy.1, hy.2]
  have hsum : x + (y - x) = y := by ring
  calc
    |y| = |x + (y - x)| := by rw [hsum]
    _ ≤ |x| + |y - x| := abs_add_le x (y - x)
    _ ≤ |x| + 1 := by linarith [hdist.le]

/-- Local summable majorant for the derivative terms of the Gaussian Zak `h₀`
series near a fixed spatial point. -/
theorem gaussianH0C_zak_deriv_local_bound
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧
      ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioo (x - 1) (x + 1) →
        ‖deriv gaussianH0C (y - γ * (k : ℝ)) * Zak.zakPhase γ k ω‖ ≤ u k := by
  let R : ℝ := |x| + 1
  let E : ℤ → ℝ := fun k =>
    Real.exp (-Real.pi * (γ ^ 2 * (k : ℝ) ^ 2 - 2 * (γ * R) * |(k : ℝ)|))
  let u : ℤ → ℝ := fun k =>
    (2 * Real.pi) * (R * E k + γ * (|(k : ℝ)| * E k))
  have hT : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hE : Summable E := by
    have htheta := summable_pow_mul_jacobiTheta₂_term_bound (γ * R) hT 0
    simpa [E] using htheta
  have hE1 : Summable fun k : ℤ => |(k : ℝ)| * E k := by
    have htheta := summable_pow_mul_jacobiTheta₂_term_bound (γ * R) hT 1
    simpa [E] using htheta
  have hu : Summable u := by
    have hR : Summable fun k : ℤ => R * E k := hE.mul_left R
    have hγE : Summable fun k : ℤ => γ * (|(k : ℝ)| * E k) := hE1.mul_left γ
    simpa [u] using (hR.add hγE).mul_left (2 * Real.pi)
  refine ⟨u, hu, ?_⟩
  intro k y hy
  have hyabs : |y| ≤ R := by
    simpa [R] using abs_le_abs_add_one_of_mem_Ioo (x := x) (y := y) hy
  have habs : |y - γ * (k : ℝ)| ≤ R + γ * |(k : ℝ)| := by
    calc
      |y - γ * (k : ℝ)| ≤ |y| + |γ * (k : ℝ)| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le y (-(γ * (k : ℝ)))
      _ = |y| + γ * |(k : ℝ)| := by rw [abs_mul, abs_of_nonneg hγ.le]
      _ ≤ R + γ * |(k : ℝ)| := by linarith [hyabs]
  have hquad : γ ^ 2 * (k : ℝ) ^ 2 - 2 * (γ * R) * |(k : ℝ)| ≤
      (y - γ * (k : ℝ)) ^ 2 := by
    have hny : (k : ℝ) * y ≤ |(k : ℝ)| * R := by
      calc
        (k : ℝ) * y ≤ |(k : ℝ) * y| := le_abs_self _
        _ = |(k : ℝ)| * |y| := abs_mul _ _
        _ ≤ |(k : ℝ)| * R := mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
    have hmul : γ * ((k : ℝ) * y) ≤ γ * (|(k : ℝ)| * R) :=
      mul_le_mul_of_nonneg_left hny hγ.le
    nlinarith [sq_nonneg y]
  have hexp : Real.exp (-Real.pi * (y - γ * (k : ℝ)) ^ 2) ≤ E k := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hprod : |y - γ * (k : ℝ)| * Real.exp (-Real.pi * (y - γ * (k : ℝ)) ^ 2) ≤
      (R + γ * |(k : ℝ)|) * E k := by
    refine mul_le_mul habs hexp (Real.exp_nonneg _) ?_
    have hR_nonneg : 0 ≤ R := by dsimp [R]; positivity
    have hγabs : 0 ≤ γ * |(k : ℝ)| := mul_nonneg hγ.le (abs_nonneg _)
    linarith
  have htwopi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  rw [norm_deriv_gaussianH0C_mul_zakPhase]
  calc
    (2 * Real.pi) * |y - γ * (k : ℝ)| * Real.exp (-Real.pi * (y - γ * (k : ℝ)) ^ 2)
        = (2 * Real.pi) *
            (|y - γ * (k : ℝ)| * Real.exp (-Real.pi * (y - γ * (k : ℝ)) ^ 2)) := by
          ring
    _ ≤ (2 * Real.pi) * ((R + γ * |(k : ℝ)|) * E k) := by
      exact mul_le_mul_of_nonneg_left hprod htwopi_nonneg
    _ = u k := by
      dsimp [u]
      ring

/-- Local summable majorant package for differentiating the Gaussian Zak `h₀`
series term by term near a fixed spatial point.  The base `h₀` Zak series
summability is now proved from the theta summability bound; only the local
derivative majorant remains as a residual. -/
theorem gaussianH0C_zak_deriv_local_summable_majorant
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧
      Summable (fun k : ℤ =>
        gaussianH0C (x - γ * (k : ℝ)) * Zak.zakPhase γ k ω) ∧
      ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioo (x - 1) (x + 1) →
        ‖deriv gaussianH0C (y - γ * (k : ℝ)) * Zak.zakPhase γ k ω‖ ≤ u k := by
  rcases gaussianH0C_zak_deriv_local_bound γ hγ x ω with ⟨u, hu, hbound⟩
  exact ⟨u, hu, summable_gaussianH0C_zakPhase_of_pos γ hγ x ω, hbound⟩

/-- Smooth-series reduction of the derivative-commutation step for the
Gaussian Zak `h₀` transform from a local summable derivative majorant. -/
lemma gaussianZakH0_deriv_commutes_of_local_bound
    (γ : ℝ) (x ω : ℝ) {u : ℤ → ℝ}
    (hu : Summable u)
    (hbound : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioo (x - 1) (x + 1) →
      ‖deriv gaussianH0C (y - γ * (k : ℝ)) * Zak.zakPhase γ k ω‖ ≤ u k)
    (h0 : Summable fun k : ℤ =>
      gaussianH0C (x - γ * (k : ℝ)) * Zak.zakPhase γ k ω) :
    deriv (fun y : ℝ => Zak.zakTransform γ gaussianH0C y ω) x =
      Zak.zakTransform γ (fun t : ℝ => deriv gaussianH0C t) x ω := by
  let U : Set ℝ := Set.Ioo (x - 1) (x + 1)
  have hU_open : IsOpen U := isOpen_Ioo
  have hU_pre : IsPreconnected U := isPreconnected_Ioo
  have hxmem : x ∈ U := by
    dsimp [U]
    constructor <;> linarith
  let g : ℤ → ℝ → ℂ := fun k y =>
    gaussianH0C (y - γ * (k : ℝ)) * Zak.zakPhase γ k ω
  let gd : ℤ → ℝ → ℂ := fun k y =>
    deriv gaussianH0C (y - γ * (k : ℝ)) * Zak.zakPhase γ k ω
  have hg : ∀ k y, y ∈ U → HasDerivAt (g k) (gd k y) y := by
    intro k y _hy
    have hinner : HasDerivAt (fun y : ℝ => y - γ * (k : ℝ)) 1 y := by
      simpa using (hasDerivAt_id y).sub_const (γ * (k : ℝ))
    have hcomp : HasDerivAt (gaussianH0C ∘ fun y : ℝ => y - γ * (k : ℝ))
        (deriv gaussianH0C (y - γ * (k : ℝ))) y := by
      have hraw := (hasDerivAt_gaussianH0C (y - γ * (k : ℝ))).scomp y hinner
      simpa only [one_smul, deriv_gaussianH0C] using hraw
    simpa [g, gd, Function.comp] using hcomp.mul_const (Zak.zakPhase γ k ω)
  have hgd : ∀ k y, y ∈ U → ‖gd k y‖ ≤ u k := by
    intro k y hy
    simpa [gd] using hbound k y hy
  have htsum := hasDerivAt_tsum_of_isPreconnected
    (u := u) (t := U) hu hU_open hU_pre hg hgd hxmem (by simpa [g] using h0) hxmem
  simpa [g, gd, Zak.zakTransform_eq_tsum_zakPhase, Zak.zakPhase] using htsum.deriv

/-- Termwise derivative commutation for the `h₀` Zak transform, reduced to the
local Gaussian majorant above. -/
theorem gaussianZakH0_deriv_commutes
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    deriv (fun y : ℝ => Zak.zakTransform γ gaussianH0C y ω) x =
      Zak.zakTransform γ (fun t : ℝ => deriv gaussianH0C t) x ω := by
  rcases gaussianH0C_zak_deriv_local_summable_majorant γ hγ x ω with
    ⟨u, hu, h0, hbound⟩
  exact gaussianZakH0_deriv_commutes_of_local_bound γ x ω hu hbound h0

/-- The termwise derivative commutation plus the Gaussian derivative identity
converts the `h₀` Zak transform into the first-Hermite `h₁` Zak transform. -/
theorem gaussianZakH1_deriv_bridge
    (γ : ℝ) (hγ : 0 < γ) (x ω : ℝ) :
    Zak.zakTransform γ gaussianH1C x ω =
      (-(2 * (Real.pi : ℂ)))⁻¹ *
        deriv (fun y : ℝ => Zak.zakTransform γ gaussianH0C y ω) x := by
  let c : ℂ := (-(2 * (Real.pi : ℂ)))⁻¹
  have hfun : gaussianH1C = fun t : ℝ => c * deriv gaussianH0C t := by
    funext t
    exact gaussianH1C_eq_deriv_gaussianH0C t
  rw [hfun, zakTransform_const_mul]
  rw [gaussianZakH0_deriv_commutes γ hγ x ω]
end LyubarskiiNes.RationalDensity
