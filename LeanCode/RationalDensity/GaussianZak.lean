import LeanCode.ZakTransform.Criterion

namespace LyubarskiiNes.RationalDensity

noncomputable def gaussianH0 (t : ℝ) : ℝ := Real.exp (-Real.pi * t ^ 2)

noncomputable def gaussianH1 (t : ℝ) : ℝ := t * Real.exp (-Real.pi * t ^ 2)

noncomputable def gaussianH0C (t : ℝ) : ℂ := gaussianH0 t

noncomputable def gaussianH1C (t : ℝ) : ℂ := gaussianH1 t

/-- The complex-valued Gaussian has the expected real norm. -/
lemma norm_gaussianH0C (t : ℝ) :
    ‖gaussianH0C t‖ = Real.exp (-Real.pi * t ^ 2) := by
  unfold gaussianH0C gaussianH0
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.exp_pos _).le

/-- The first-Hermite Gaussian sample norm is `|t|` times the Gaussian. -/
lemma norm_gaussianH1C (t : ℝ) :
    ‖gaussianH1C t‖ = |t| * Real.exp (-Real.pi * t ^ 2) := by
  unfold gaussianH1C gaussianH1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [abs_of_nonneg (Real.exp_pos _).le]

noncomputable def gaussianZakPhaseSlope (ω : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)

noncomputable def gaussianZakPhase (ω y : ℝ) : ℂ :=
  Complex.exp (gaussianZakPhaseSlope ω * (y : ℂ))

noncomputable def gaussianZakThetaArg (γ ω y : ℝ) : ℂ :=
  ((γ : ℂ)⁻¹) * (y : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ)

noncomputable def gaussianZakTau (γ : ℝ) : ℂ :=
  Complex.I / (γ : ℂ) ^ 2

noncomputable def gaussianZakDTheta (γ ω y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      jacobiTheta₂' (gaussianZakThetaArg γ ω y) (gaussianZakTau γ) +
    (γ : ℂ) * (ω : ℂ) *
      LyubarskiiNes.theta (gaussianZakThetaArg γ ω y) (gaussianZakTau γ)

noncomputable def gaussianZakH0ClosedForm (γ ω y : ℝ) : ℂ :=
  (γ : ℂ)⁻¹ * Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
    (gaussianZakPhase ω y *
      LyubarskiiNes.theta (gaussianZakThetaArg γ ω y) (gaussianZakTau γ))

noncomputable def gaussianZakH1ClosedForm (γ ω y : ℝ) : ℂ :=
  -Complex.I / (γ : ℂ) ^ 2 * Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
    gaussianZakPhase ω y * gaussianZakDTheta γ ω y

/-- The exponential phase factor in the Gaussian Zak formula is nonzero. -/
lemma gaussianZakPhase_ne_zero (ω y : ℝ) :
    gaussianZakPhase ω y ≠ 0 := by
  unfold gaussianZakPhase
  exact Complex.exp_ne_zero _

/-- The differential identity `h₀' = -2π h₁` for the real Gaussian. -/
lemma hasDerivAt_gaussianH0 (t : ℝ) :
    HasDerivAt gaussianH0 (-(2 * Real.pi) * gaussianH1 t) t := by
  unfold gaussianH0 gaussianH1
  have hquad : HasDerivAt (fun x : ℝ => -Real.pi * x ^ (2 : ℕ)) (-Real.pi * (2 * t)) t := by
    simpa using (((hasDerivAt_id t).pow 2).const_mul (-Real.pi))
  convert hquad.exp using 1
  ring

/-- Complex-valued version of `h₀' = -2π h₁`, for Zak-series summands. -/
lemma hasDerivAt_gaussianH0C (t : ℝ) :
    HasDerivAt gaussianH0C ((-(2 * Real.pi) : ℝ) * gaussianH1C t) t := by
  unfold gaussianH0C gaussianH1C
  simpa [Complex.ofReal_mul] using (hasDerivAt_gaussianH0 t).ofReal_comp

/-- The ordinary derivative form of `h₀' = -2π h₁`. -/
lemma deriv_gaussianH0C (t : ℝ) :
    deriv gaussianH0C t = ((-(2 * Real.pi) : ℝ) : ℂ) * gaussianH1C t := by
  exact (hasDerivAt_gaussianH0C t).deriv

/-- Solves the Gaussian derivative identity for the first Hermite factor. -/
lemma gaussianH1C_eq_deriv_gaussianH0C (t : ℝ) :
    gaussianH1C t = (-(2 * (Real.pi : ℂ)))⁻¹ * deriv gaussianH0C t := by
  rw [deriv_gaussianH0C]
  have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  field_simp [hne]
  simp [mul_comm, mul_assoc]

/-- Derivative of a complex affine function of one real variable. -/
lemma hasDerivAt_complex_affine (slope intercept : ℂ) (y : ℝ) :
    HasDerivAt (fun x : ℝ => slope * (x : ℂ) + intercept) slope y := by
  have hlin : HasDerivAt (fun x : ℝ => slope * (x : ℂ)) slope y := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul slope)
  exact hlin.add_const intercept

/-- The Gaussian-Zak theta parameter `i / γ²` lies in the upper half-plane. -/
lemma gaussianZakTau_im_pos {γ : ℝ} (hγ : 0 < γ) :
    0 < (Complex.I / (γ : ℂ) ^ 2).im := by
  have hpow : (γ : ℂ) ^ 2 = ((γ ^ 2 : ℝ) : ℂ) := by
    norm_num [pow_two, Complex.ofReal_mul]
  rw [hpow, Complex.div_im]
  simp only [Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, one_mul,
    zero_mul]
  dsimp [Complex.normSq]
  ring_nf
  positivity

/-- The Gaussian-Zak theta argument is continuous as a function of `(y,ω)`. -/
lemma continuous_gaussianZakThetaArg (γ : ℝ) :
    Continuous fun z : ℝ × ℝ => gaussianZakThetaArg γ z.2 z.1 := by
  unfold gaussianZakThetaArg
  continuity

/-- Joint continuity of the theta factor in the Gaussian-Zak closed form. -/
lemma continuous_gaussianZakTheta (γ : ℝ) (hγ : 0 < γ) :
    Continuous fun z : ℝ × ℝ =>
      LyubarskiiNes.theta (gaussianZakThetaArg γ z.2 z.1) (gaussianZakTau γ) := by
  have harg : Continuous fun z : ℝ × ℝ => gaussianZakThetaArg γ z.2 z.1 :=
    continuous_gaussianZakThetaArg γ
  have hpair : Continuous fun z : ℝ × ℝ =>
      (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ) := by
    exact harg.prodMk continuous_const
  have hτ : 0 < (gaussianZakTau γ).im := gaussianZakTau_im_pos hγ
  rw [continuous_iff_continuousAt]
  intro z
  have hpz : ContinuousAt (fun z : ℝ × ℝ =>
      (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ)) z := hpair.continuousAt
  exact ContinuousAt.comp (x := z)
    (f := fun z : ℝ × ℝ => (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
    (continuousAt_jacobiTheta₂ (gaussianZakThetaArg γ z.2 z.1) hτ) hpz

/-- Joint continuity of the theta-derivative factor in the Gaussian-Zak closed
form. -/
lemma continuous_gaussianZakTheta_deriv (γ : ℝ) (hγ : 0 < γ) :
    Continuous fun z : ℝ × ℝ =>
      jacobiTheta₂' (gaussianZakThetaArg γ z.2 z.1) (gaussianZakTau γ) := by
  have harg : Continuous fun z : ℝ × ℝ => gaussianZakThetaArg γ z.2 z.1 :=
    continuous_gaussianZakThetaArg γ
  have hpair : Continuous fun z : ℝ × ℝ =>
      (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ) := by
    exact harg.prodMk continuous_const
  have hτ : 0 < (gaussianZakTau γ).im := gaussianZakTau_im_pos hγ
  rw [continuous_iff_continuousAt]
  intro z
  have hpz : ContinuousAt (fun z : ℝ × ℝ =>
      (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ)) z := hpair.continuousAt
  exact ContinuousAt.comp (x := z)
    (f := fun z : ℝ × ℝ => (gaussianZakThetaArg γ z.2 z.1, gaussianZakTau γ))
    (g := fun p : ℂ × ℂ => jacobiTheta₂' p.1 p.2)
    (continuousAt_jacobiTheta₂' (gaussianZakThetaArg γ z.2 z.1) hτ) hpz

/-- Joint continuity of the first-Hermite Gaussian-Zak closed form. -/
lemma continuous_gaussianZakH1ClosedForm (γ : ℝ) (hγ : 0 < γ) :
    Continuous fun z : ℝ × ℝ => gaussianZakH1ClosedForm γ z.2 z.1 := by
  have htheta := continuous_gaussianZakTheta γ hγ
  have htheta' := continuous_gaussianZakTheta_deriv γ hγ
  unfold gaussianZakH1ClosedForm gaussianZakDTheta gaussianZakPhase gaussianZakPhaseSlope
  continuity

/-- Derivative of the phase factor `exp(2π i ω y)`. -/
lemma hasDerivAt_gaussianZakPhase (ω y : ℝ) :
    HasDerivAt (fun x : ℝ => gaussianZakPhase ω x)
      (gaussianZakPhaseSlope ω * gaussianZakPhase ω y) y := by
  unfold gaussianZakPhase
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_complex_affine (gaussianZakPhaseSlope ω) 0 y).cexp)

/-- Chain-rule form of the theta derivative along a real affine line. -/
lemma hasDerivAt_theta_comp_affine
    (τ slope intercept : ℂ) (hτ : 0 < τ.im) (y : ℝ) :
    HasDerivAt (fun x : ℝ => LyubarskiiNes.theta (slope * (x : ℂ) + intercept) τ)
      (jacobiTheta₂' (slope * (y : ℂ) + intercept) τ * slope) y := by
  exact (hasDerivAt_jacobiTheta₂_fst (slope * (y : ℂ) + intercept) hτ).comp y
    (hasDerivAt_complex_affine slope intercept y)

/-- Product-rule derivative for the phase times the affine theta factor. -/
lemma hasDerivAt_phase_mul_theta_comp_affine
    (ω : ℝ) (τ slope intercept : ℂ) (hτ : 0 < τ.im) (y : ℝ) :
    HasDerivAt
      (fun x : ℝ => gaussianZakPhase ω x *
        LyubarskiiNes.theta (slope * (x : ℂ) + intercept) τ)
      (gaussianZakPhaseSlope ω * gaussianZakPhase ω y *
          LyubarskiiNes.theta (slope * (y : ℂ) + intercept) τ +
        gaussianZakPhase ω y *
          (jacobiTheta₂' (slope * (y : ℂ) + intercept) τ * slope)) y := by
  exact (hasDerivAt_gaussianZakPhase ω y).mul
    (hasDerivAt_theta_comp_affine τ slope intercept hτ y)

/--
Specialized derivative of the phase-theta factor appearing in the Gaussian
Zak formula, with `τ = i / γ²` and `z = y / γ + iω / γ`.
-/
lemma hasDerivAt_gaussianZakPhase_mul_theta (γ : ℝ) (hγ : 0 < γ) (ω y : ℝ) :
    HasDerivAt
      (fun x : ℝ => gaussianZakPhase ω x *
        LyubarskiiNes.theta (((γ : ℂ)⁻¹) * (x : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
          (Complex.I / (γ : ℂ) ^ 2))
      (gaussianZakPhaseSlope ω * gaussianZakPhase ω y *
          LyubarskiiNes.theta (((γ : ℂ)⁻¹) * (y : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
            (Complex.I / (γ : ℂ) ^ 2) +
        gaussianZakPhase ω y *
          (jacobiTheta₂'
            (((γ : ℂ)⁻¹) * (y : ℂ) + Complex.I * (ω : ℂ) / (γ : ℂ))
            (Complex.I / (γ : ℂ) ^ 2) * ((γ : ℂ)⁻¹))) y := by
  exact hasDerivAt_phase_mul_theta_comp_affine ω (Complex.I / (γ : ℂ) ^ 2)
    ((γ : ℂ)⁻¹) (Complex.I * (ω : ℂ) / (γ : ℂ)) (gaussianZakTau_im_pos hγ) y

/--
Derivative of the closed-form right hand side for the Gaussian Zak formula.
This is the analytic chain/product rule part of the future `Zgamma_h0_eq`.
-/
lemma hasDerivAt_gaussianZakH0ClosedForm (γ : ℝ) (hγ : 0 < γ) (ω y : ℝ) :
    HasDerivAt (fun x : ℝ => gaussianZakH0ClosedForm γ ω x)
      ((γ : ℂ)⁻¹ * Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2) *
        (gaussianZakPhaseSlope ω * gaussianZakPhase ω y *
          LyubarskiiNes.theta (gaussianZakThetaArg γ ω y) (gaussianZakTau γ) +
        gaussianZakPhase ω y *
          (jacobiTheta₂' (gaussianZakThetaArg γ ω y) (gaussianZakTau γ) *
            ((γ : ℂ)⁻¹)))) y := by
  unfold gaussianZakH0ClosedForm gaussianZakThetaArg gaussianZakTau
  exact (hasDerivAt_gaussianZakPhase_mul_theta γ hγ ω y).const_mul
    ((γ : ℂ)⁻¹ * Complex.exp (-(Real.pi : ℂ) * (ω : ℂ) ^ 2))

/--
Constant bookkeeping converting the derivative of the `h₀` closed form into
the paper's `D_{γω}` closed form for `h₁`.
-/
lemma gaussianZakH1ClosedForm_eq_neg_inv_two_pi_deriv
    (γ : ℝ) (hγ : 0 < γ) (ω y : ℝ) :
    gaussianZakH1ClosedForm γ ω y =
      (-(2 * (Real.pi : ℂ)))⁻¹ *
        deriv (fun x : ℝ => gaussianZakH0ClosedForm γ ω x) y := by
  rw [(hasDerivAt_gaussianZakH0ClosedForm γ hγ ω y).deriv]
  unfold gaussianZakH1ClosedForm gaussianZakDTheta gaussianZakThetaArg gaussianZakTau
    gaussianZakPhaseSlope
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hγ
  have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hγc, hpic, Complex.I_mul_I]
  ring_nf

/--
The first-Hermite-specific derivative conversion in the Gaussian Zak formula.

The remaining analytic work is not this constant/chain-rule bookkeeping, but
the concrete `Zgamma_h0_eq` identity and the termwise Zak-derivative bridge
needed to transport that identity through the Zak transform.
-/
theorem Zgamma_h1_eq (γ : ℝ) (hγ : 0 < γ) (ω y : ℝ) :
    gaussianZakH1ClosedForm γ ω y =
      (-(2 * (Real.pi : ℂ)))⁻¹ *
        deriv (fun x : ℝ => gaussianZakH0ClosedForm γ ω x) y :=
  gaussianZakH1ClosedForm_eq_neg_inv_two_pi_deriv γ hγ ω y

end LyubarskiiNes.RationalDensity
