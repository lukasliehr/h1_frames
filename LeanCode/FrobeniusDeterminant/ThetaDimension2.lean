import LeanCode.FrobeniusDeterminant.ThetaDimension
open Complex Topology Filter
namespace LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
open scoped Real

/-! ## Base case: 𝒯_1 vanishing (verified WF_ThetaVanish) -/

/-! ## Preliminary: θ = deltaX T ((1+T)/2), θ ∈ ThetaSpace 1 0 T -/

/-! ## Periodicity of h = f/θ (junk-safe) -/

theorem h_periodic_one {T : ℂ} {f : ℂ → ℂ} (hf : f ∈ ThetaSpace 1 0 T) :
    Function.Periodic (fun z => f z / jacobiTheta₂ z T) 1 := by
  intro z
  simp only
  rw [hf.2.1 z, jacobiTheta₂_add_left]

theorem h_periodic_tau {T : ℂ} {f : ℂ → ℂ} (hf : f ∈ ThetaSpace 1 0 T) :
    Function.Periodic (fun z => f z / jacobiTheta₂ z T) T := by
  intro z
  simp only
  rw [hf.2.2 z, jacobiTheta₂_add_left']
  -- autFactor 1 0 T z = exp(-πi·T - 2πi·z) = exp(-πi(T+2z))
  have hfac : autFactor 1 0 T z = Complex.exp (-↑Real.pi * I * (T + 2 * z)) := by
    unfold autFactor
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨0, ?_⟩
    push_cast; ring
  rw [hfac, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-! ## The removable-extension integrand g is holomorphic on the cell neighbourhood -/

/-- `g = f/θ − r/(·−ζ)` (pole removed) is differentiable on the cell neighbourhood. -/
theorem differentiableOn_ratio_sub_cellNbhd {T : ℂ} (hT : 0 < T.im) {f u : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hu : AnalyticAt ℂ u ((1 + T) / 2)) (hune : u ((1 + T) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z T) =ᶠ[nhds ((1 + T) / 2)]
      fun z => (z - (1 + T) / 2) ^ 1 • u z) :
    DifferentiableOn ℂ
      (Function.update
        (fun z => f z / jacobiTheta₂ z T - (f ((1+T)/2) / u ((1+T)/2)) / (z - (1 + T) / 2))
        ((1 + T) / 2)
        (dslope (fun z => f z / u z) ((1+T)/2) ((1+T)/2)))
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd T) := by
  intro z hz
  by_cases hzζ : z = (1 + T) / 2
  · subst hzζ
    exact (differentiableAt_ratio_sub_extend (hf ((1+T)/2)) hu hune hfac).differentiableWithinAt
  · -- away from ζ: update is inert, θ ≠ 0
    have hθ0 : jacobiTheta₂ z T ≠ 0 :=
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_ne_zero_cellNbhd hT hz hzζ
    have hznez : z - (1 + T) / 2 ≠ 0 := sub_ne_zero.mpr hzζ
    -- On a neighbourhood of z (within cellNbhd is enough), the update equals the raw function.
    have hda : DifferentiableAt ℂ
        (fun w => f w / jacobiTheta₂ w T - (f ((1+T)/2) / u ((1+T)/2)) / (w - (1 + T) / 2)) z := by
      have hθan : AnalyticAt ℂ (fun w => jacobiTheta₂ w T) z := theta_analyticAt hT z
      refine DifferentiableAt.sub ?_ ?_
      · exact (hf z).differentiableAt.div hθan.differentiableAt hθ0
      · exact differentiableAt_const _ |>.div
          ((differentiableAt_id.sub (differentiableAt_const _))) hznez
    -- the update agrees with hda's function on 𝓝 z (since z ≠ ζ, and update only changes value at ζ)
    have heq : Function.update
        (fun z => f z / jacobiTheta₂ z T - (f ((1+T)/2) / u ((1+T)/2)) / (z - (1 + T) / 2))
        ((1 + T) / 2)
        (dslope (fun z => f z / u z) ((1+T)/2) ((1+T)/2))
        =ᶠ[nhds z]
        (fun w => f w / jacobiTheta₂ w T - (f ((1+T)/2) / u ((1+T)/2)) / (w - (1 + T) / 2)) := by
      filter_upwards [isOpen_ne.mem_nhds hzζ] with w hw
      exact Function.update_of_ne hw _ _
    exact ((hda.congr_of_eventuallyEq heq)).differentiableWithinAt

/-- `∮_∂P (f/θ − r/(·−ζ)) = 0`: the integrand agrees on the contour with its removable
extension `g` (they differ only at `ζ`, off the contour by `sides_ne_zeta`), and `g` is holomorphic
on the whole cell. -/
theorem theta_ratio_contour_g_zero {T : ℂ} (hT : 0 < T.im) {f u : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hu : AnalyticAt ℂ u ((1 + T) / 2)) (hune : u ((1 + T) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z T) =ᶠ[nhds ((1 + T) / 2)]
      fun z => (z - (1 + T) / 2) ^ 1 • u z) :
    ResidueTheorem.parContourIntegral
      (fun z => f z / jacobiTheta₂ z T - (f ((1+T)/2) / u ((1+T)/2)) / (z - (1 + T) / 2)) 0 T = 0 := by
  set g : ℂ → ℂ :=
    fun z => f z / jacobiTheta₂ z T - (f ((1+T)/2) / u ((1+T)/2)) / (z - (1 + T) / 2) with hg
  set gext := Function.update g ((1 + T) / 2)
    (dslope (fun z => f z / u z) ((1+T)/2) ((1+T)/2)) with hgext
  have hgext0 : ResidueTheorem.parContourIntegral gext 0 T = 0 :=
    ResidueTheorem.parContourIntegral_eq_zero_of_holo _
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd T)
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.isOpen_cellNbhd T)
      (differentiableOn_ratio_sub_cellNbhd hT hf hu hune hfac) 0 T
      (fun s t hs ht => by simpa using cell_subset_cellNbhd hT s t hs ht)
  have hupd : ∀ w : ℂ, w ≠ (1 + T) / 2 → g w = gext w :=
    fun w hw => (Function.update_of_ne hw _ g).symm
  have key : ResidueTheorem.parContourIntegral g 0 T
      = ResidueTheorem.parContourIntegral gext 0 T := by
    simp only [ResidueTheorem.parContourIntegral]
    rw [intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hT t).1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hT t).2.2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hT t).2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hT t).2.2.2)]
  rw [key, hgext0]

/-! ## GOAL 1 (α = 0) -/

set_option maxHeartbeats 800000 in
/-- **Every element of `𝒯_1^0(T)` vanishes at `ζ = (1+T)/2`.** -/
theorem ThetaSpace_one_vanishes_zero {T : ℂ} (hT : 0 < T.im) {f : ℂ → ℂ}
    (hf : f ∈ ThetaSpace 1 0 T) : f ((1 + T) / 2) = 0 := by
  set ζ : ℂ := (1 + T) / 2 with hζ
  -- 1. simple zero factorization of θ at ζ
  obtain ⟨u, hu, hune, hfac⟩ :=
    ((theta_analyticAt hT ζ).analyticOrderAt_eq_natCast (n := 1)).mp
      (by rw [hζ, theta_simple_zero hT]; norm_cast)
  set r : ℂ := f ζ / u ζ with hr
  -- 2. periodicity: ∮ (f/θ) 0 T = 0
  have hper0 : ResidueTheorem.parContourIntegral
      (fun z => f z / jacobiTheta₂ z T) 0 T = 0 :=
    ResidueTheorem.parContourIntegral_eq_zero _ 0 T (h_periodic_one hf) (h_periodic_tau hf)
  -- 3. integrability inputs for the split
  have hInt : ∀ (S : ℝ → ℂ), Continuous S → (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ ζ) →
      IntervalIntegrable (fun t => r * (1 / ((S t) - ζ))) MeasureTheory.volume 0 1 := by
    intro S hS hne
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      ((hS.sub continuous_const).continuousOn) (fun t ht => ?_))
    rw [sub_ne_zero]; exact hne t ht
  have hgc : ContinuousOn
      (Function.update
        (fun z => f z / jacobiTheta₂ z T - r / (z - ζ)) ζ
        (dslope (fun z => f z / u z) ζ ζ))
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd T) :=
    (differentiableOn_ratio_sub_cellNbhd hT (fun z => hf.1 z) hu hune hfac).continuousOn
  have hupd : ∀ w : ℂ, w ≠ ζ →
      (fun z => f z / jacobiTheta₂ z T - r / (z - ζ)) w
        = (Function.update (fun z => f z / jacobiTheta₂ z T - r / (z - ζ)) ζ
            (dslope (fun z => f z / u z) ζ ζ)) w :=
    fun w hw => (Function.update_of_ne hw (dslope (fun z => f z / u z) ζ ζ)
      (fun z => f z / jacobiTheta₂ z T - r / (z - ζ))).symm
  have gInt : ∀ (S : ℝ → ℂ), Continuous S →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd T) →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ ζ) →
      IntervalIntegrable
        (fun t => f (S t) / jacobiTheta₂ (S t) T - r / ((S t) - ζ))
        MeasureTheory.volume 0 1 := by
    intro S hS hmem hne
    apply ContinuousOn.intervalIntegrable
    exact (hgc.comp hS.continuousOn hmem).congr (fun t ht => hupd (S t) (hne t ht))
  -- 4. split f/θ = r·(1/(·-ζ)) + (f/θ - r/(·-ζ))
  have heq : (fun z => f z / jacobiTheta₂ z T)
      = fun z => r * (1 / (z - ζ)) + (f z / jacobiTheta₂ z T - r / (z - ζ)) := by
    funext z; rw [mul_one_div]; ring
  rw [heq, ResidueTheorem.parContourIntegral_split
      (fun z => r * (1 / (z - ζ)))
      (fun z => f z / jacobiTheta₂ z T - r / (z - ζ)) 0 T
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hT t).1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hT t).2.2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hT t).2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hT t).2.2.2))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hT t ht).1)
        (fun t _ => (sides_ne_zeta hT t).1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hT t ht).2.1)
        (fun t _ => (sides_ne_zeta hT t).2.2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hT t ht).2.2.1)
        (fun t _ => (sides_ne_zeta hT t).2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hT t ht).2.2.2)
        (fun t _ => (sides_ne_zeta hT t).2.2.2))] at hper0
  rw [ResidueTheorem.parContourIntegral_const_mul] at hper0
  -- g-part vanishes
  have hgzero : ResidueTheorem.parContourIntegral
      (fun z => f z / jacobiTheta₂ z T - r / (z - ζ)) 0 T = 0 := by
    have := theta_ratio_contour_g_zero hT (fun z => hf.1 z) hu hune hfac
    simpa [hr, hζ] using this
  rw [hgzero, add_zero] at hper0
  -- the pole part is 2πi
  have hpole : ResidueTheorem.parContourIntegral (fun z => 1 / (z - ζ)) 0 T
      = 2 * (Real.pi : ℂ) * I := by
    have := ResidueTheorem.parContourIntegral_inv_eq ζ T hT
    simpa [hζ] using this
  rw [hpole] at hper0
  -- 0 = r · 2πi ⟹ r = 0 ⟹ f ζ = 0
  have h2πne : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hr0 : r = 0 := by
    exact (mul_eq_zero.mp hper0).resolve_right h2πne
  -- r = f ζ / u ζ = 0 with u ζ ≠ 0 ⟹ f ζ = 0
  rw [hr, div_eq_zero_iff] at hr0
  exact hr0.resolve_right hune

/-! ## GOAL 2 (general α) via translation -/

/-- Translation `f̃(z) = f(z+α)` maps `𝒯_1^α(T)` into `𝒯_1^0(T)`. -/
theorem translate_mem_ThetaSpace_zero {T α : ℂ} {f : ℂ → ℂ} (hf : f ∈ ThetaSpace 1 α T) :
    (fun z => f (z + α)) ∈ ThetaSpace 1 0 T := by
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · have hinner : AnalyticAt ℂ (fun w : ℂ => w + α) z := analyticAt_id.add analyticAt_const
    have hcomp : AnalyticAt ℂ ((fun w => f w) ∘ (fun w : ℂ => w + α)) z :=
      AnalyticAt.comp (hf.1 (z + α)) hinner
    exact hcomp
  · simp only
    rw [show z + 1 + α = (z + α) + 1 by ring, hf.2.1 (z + α)]
  · simp only
    rw [show z + T + α = (z + α) + T by ring, hf.2.2 (z + α)]
    have hfac : autFactor 1 α T (z + α) = autFactor 1 0 T z := by
      unfold autFactor
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨0, by push_cast; ring⟩
    rw [hfac]

set_option maxHeartbeats 800000 in
/-- **Every element of `𝒯_1^α(T)` vanishes at `α + (1+T)/2`.** -/
theorem ThetaSpace_one_vanishes {T α : ℂ} (hT : 0 < T.im) {f : ℂ → ℂ}
    (hf : f ∈ ThetaSpace 1 α T) : f (α + (1 + T) / 2) = 0 := by
  have hft := translate_mem_ThetaSpace_zero hf
  have h0 := ThetaSpace_one_vanishes_zero hT hft
  rw [show α + (1 + T) / 2 = (1 + T) / 2 + α by ring]
  exact h0

/-! ## Φ_r residue basis (independence) -/

section
/-! ## Residue-sum functions `Φ_r` (the level-`q` theta basis).

Fix `τ` with `0 < τ.im`, and `q` with `0 < q`.  For `r : ℤ` define
`Phi τ q r z = Σ'_ℓ jacobiTheta₂_term (qℓ+r) z τ`. -/

variable {τ : ℂ} {q : ℕ}

/-- The residue-`r` partial theta sum. -/
noncomputable def Phi (τ : ℂ) (q : ℕ) (r : ℤ) (z : ℂ) : ℂ :=
    ∑' ℓ : ℤ, jacobiTheta₂_term ((q:ℤ)*ℓ + r) z τ

/-- `(q²τ).im > 0` whenever `0 < τ.im` and `0 < q`. -/
theorem qsq_im_pos (hτ : 0 < τ.im) (hq : 0 < q) : 0 < ((q:ℂ)^2*τ).im := by
  rw [Complex.mul_im]
  have h1 : ((q:ℂ)^2).im = 0 := by
    rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring]; exact Complex.natCast_im _
  have h2 : ((q:ℂ)^2).re = (q:ℝ)^2 := by
    rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring, Complex.natCast_re]; push_cast; ring
  rw [h1, h2, zero_mul, add_zero]
  exact mul_pos (by positivity) hτ

/-- **Closed form of `Φ_r`** as a scaled theta of modulus `q²τ`. -/
theorem Phi_eq (hτ : 0 < τ.im) (hq : 0 < q) (r : ℤ) (z : ℂ) :
    Phi τ q r z
      = jacobiTheta₂_term r z τ * jacobiTheta₂ ((q:ℂ)*(z + (r:ℂ)*τ)) ((q:ℂ)^2*τ) := by
  rw [Phi, residue_partial_theta hq r z τ hτ]

/-- **Target 1 — `Φ_r` is not identically zero.**  There is a point where `Φ_r ≠ 0`. -/
theorem Phi_ne_zero (hτ : 0 < τ.im) (hq : 0 < q) (r : ℤ) :
    ∃ z : ℂ, Phi τ q r z ≠ 0 := by
  -- pick z₀ where θ(·, q²τ) ≠ 0, then solve q(z+rτ) = z₀.
  obtain ⟨z₀, hz₀⟩ := ThetaZeroCount.theta_ne_zero_somewhere (qsq_im_pos hτ hq)
  have hq0 : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  refine ⟨z₀/(q:ℂ) - (r:ℂ)*τ, ?_⟩
  rw [Phi_eq hτ hq r]
  have harg : (q:ℂ)*((z₀/(q:ℂ) - (r:ℂ)*τ) + (r:ℂ)*τ) = z₀ := by
    field_simp; ring
  rw [harg]
  exact mul_ne_zero (Complex.exp_ne_zero _) hz₀

/-- **Target 2 — quasi-periodicity of `Φ_r` under the `1/q` shift.** -/
theorem Phi_shift (r : ℤ) (z : ℂ) :
    Phi τ q r (z + 1/(q:ℂ)) = Complex.exp (2*(Real.pi:ℂ)*I*(r:ℂ)/(q:ℂ)) * Phi τ q r z := by
  by_cases hq0 : (q:ℂ) = 0
  · -- degenerate q = 0 : both sides collapse trivially since 1/q = 0.
    simp only [Phi, hq0, div_zero, add_zero, Complex.exp_zero, one_mul]
  · -- termwise: term_{qℓ+r}(z+1/q) = exp(2πir/q) · term_{qℓ+r}(z).
    rw [Phi, Phi]
    have hterm : ∀ ℓ : ℤ,
        jacobiTheta₂_term ((q:ℤ)*ℓ + r) (z + 1/(q:ℂ)) τ
          = Complex.exp (2*(Real.pi:ℂ)*I*(r:ℂ)/(q:ℂ))
              * jacobiTheta₂_term ((q:ℤ)*ℓ + r) z τ := by
      intro ℓ
      simp only [jacobiTheta₂_term]
      rw [← Complex.exp_add]
      -- 2πi(qℓ+r)(z+1/q) + πi(qℓ+r)²τ = 2πir/q + [2πiℓ] + (2πi(qℓ+r)z + πi(qℓ+r)²τ)
      have hsplit :
          2*(Real.pi:ℂ)*I*(((q:ℤ)*ℓ + r : ℤ):ℂ)*(z + 1/(q:ℂ))
              + (Real.pi:ℂ)*I*(((q:ℤ)*ℓ + r : ℤ):ℂ)^2*τ
            = (((ℓ : ℤ)):ℂ)*(2*(Real.pi:ℂ)*I)
              + (2*(Real.pi:ℂ)*I*(r:ℂ)/(q:ℂ)
                  + (2*(Real.pi:ℂ)*I*(((q:ℤ)*ℓ + r : ℤ):ℂ)*z
                      + (Real.pi:ℂ)*I*(((q:ℤ)*ℓ + r : ℤ):ℂ)^2*τ)) := by
        push_cast; field_simp; ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
        Complex.exp_add]
    rw [tsum_congr hterm, tsum_mul_left]

/-- **Target 3 — linear independence of `{Φ_r}_{r∈Fin q}`.**
If `Σ_r a_r · Φ_r ≡ 0` (as a function of `z`) then all `a_r = 0`. -/
theorem Phi_indep (hτ : 0 < τ.im) (hq : 0 < q) (a : Fin q → ℂ)
    (hlin : ∀ z : ℂ, ∑ r : Fin q, a r * Phi τ q (r:ℤ) z = 0) :
    ∀ r : Fin q, a r = 0 := by
  have hq0 : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  -- Step A: from the shift relation, for each fixed z and each s, the DFT values vanish.
  -- Apply dft_inversion to E r = a r * Phi_r z  ⟹  a r * Phi_r z = 0 for all r, z.
  have hpoint : ∀ z : ℂ, ∀ r : Fin q, a (r:Fin q) * Phi τ q (r:ℤ) z = 0 := by
    intro z
    apply dft_inversion hq (fun r => a r * Phi τ q (r:ℤ) z)
    intro s
    -- ∑_r (a_r Φ_r z) e^{2πi r s/q} = ∑_r a_r Φ_r (z + s/q) = 0.
    have hshift_s : ∀ r : Fin q,
        a r * Phi τ q (r:ℤ) z * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
          = a r * Phi τ q (r:ℤ) (z + (s:ℕ)/(q:ℂ)) := by
      intro r
      -- iterate the 1/q shift s times: Φ_r(z + s/q) = exp(2πi r s/q) Φ_r z.
      have hiter : Phi τ q (r:ℤ) (z + (s:ℕ)/(q:ℂ))
          = Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))) * Phi τ q (r:ℤ) z := by
        -- induction on the natural number s.val
        induction (s:ℕ) with
        | zero => simp
        | succ n ih =>
          have hstep : z + ((n+1 : ℕ):ℂ)/(q:ℂ) = (z + (n:ℕ)/(q:ℂ)) + 1/(q:ℂ) := by
            push_cast; ring
          rw [hstep, Phi_shift, ih, ← mul_assoc, ← Complex.exp_add]
          congr 2
          push_cast; field_simp; ring
      rw [hiter]; ring
    calc ∑ r : Fin q, a r * Phi τ q (r:ℤ) z
              * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
          = ∑ r : Fin q, a r * Phi τ q (r:ℤ) (z + (s:ℕ)/(q:ℂ)) :=
            Finset.sum_congr rfl (fun r _ => hshift_s r)
      _ = 0 := hlin (z + (s:ℕ)/(q:ℂ))
  -- Step B: Φ_r ≢ 0 ⟹ a_r = 0.
  intro r
  obtain ⟨z, hz⟩ := Phi_ne_zero hτ hq (r:ℤ)
  have := hpoint z r
  exact (mul_eq_zero.mp this).resolve_right hz
end

/-! ### Φ_r membership in 𝒯_q^0(qτ) -/

theorem Phi_analyticAt {q : ℕ} (hq : 0 < q) (r : ℤ) {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    AnalyticAt ℂ (Phi τ q r) z := by
  have heq : Phi τ q r = fun w => jacobiTheta₂_term r w τ
      * jacobiTheta₂ ((q : ℂ) * (w + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ) := by
    funext w; exact Phi_eq hτ hq r w
  rw [heq]
  have hterm : AnalyticAt ℂ (fun w => jacobiTheta₂_term r w τ) z := by
    unfold jacobiTheta₂_term; fun_prop
  have hθ : AnalyticAt ℂ (fun w => jacobiTheta₂ ((q : ℂ) * (w + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ)) z := by
    have hbase : AnalyticAt ℂ (fun v => jacobiTheta₂ v ((q : ℂ) ^ 2 * τ))
        ((q : ℂ) * (z + (r : ℂ) * τ)) := theta_analyticAt (qsq_im_pos hτ hq) _
    have hrw : (fun w => jacobiTheta₂ ((q : ℂ) * (w + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ))
        = (fun v => jacobiTheta₂ v ((q : ℂ) ^ 2 * τ)) ∘ (fun w => (q : ℂ) * (w + (r : ℂ) * τ)) := rfl
    rw [hrw]
    exact AnalyticAt.comp_of_eq hbase
      (show AnalyticAt ℂ (fun w => (q : ℂ) * (w + (r : ℂ) * τ)) z from by fun_prop) rfl
  exact hterm.mul hθ

theorem Phi_add_one {q : ℕ} (hq : 0 < q) (r : ℤ) {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    Phi τ q r (z + 1) = Phi τ q r z := by
  rw [Phi_eq hτ hq r, Phi_eq hτ hq r]
  have hterm : jacobiTheta₂_term r (z + 1) τ = jacobiTheta₂_term r z τ := by
    unfold jacobiTheta₂_term
    rw [show 2 * ↑Real.pi * I * (r : ℂ) * (z + 1) + ↑Real.pi * I * (r : ℂ) ^ 2 * τ
        = (2 * ↑Real.pi * I * (r : ℂ) * z + ↑Real.pi * I * (r : ℂ) ^ 2 * τ) + (r : ℂ) * (2 * ↑Real.pi * I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hθ : jacobiTheta₂ ((q : ℂ) * (z + 1 + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ)
      = jacobiTheta₂ ((q : ℂ) * (z + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ) := by
    rw [show (q : ℂ) * (z + 1 + (r : ℂ) * τ) = (q : ℂ) * (z + (r : ℂ) * τ) + ((q : ℤ) : ℂ) by push_cast; ring,
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_add_intCast]
  rw [hterm, hθ]

theorem Phi_add_ptau {q : ℕ} (hq : 0 < q) (r : ℤ) {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    Phi τ q r (z + (q : ℂ) * τ)
      = autFactor q 0 ((q : ℂ) * τ) z * Phi τ q r z := by
  rw [Phi_eq hτ hq r, Phi_eq hτ hq r]
  have hterm : jacobiTheta₂_term r (z + (q : ℂ) * τ) τ
      = Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((q : ℂ) * τ)) * jacobiTheta₂_term r z τ := by
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]; congr 1; ring
  have hθ : jacobiTheta₂ ((q : ℂ) * (z + (q : ℂ) * τ + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ)
      = Complex.exp (-↑Real.pi * I * ((q : ℂ) ^ 2 * τ + 2 * ((q : ℂ) * (z + (r : ℂ) * τ))))
        * jacobiTheta₂ ((q : ℂ) * (z + (r : ℂ) * τ)) ((q : ℂ) ^ 2 * τ) := by
    rw [show (q : ℂ) * (z + (q : ℂ) * τ + (r : ℂ) * τ)
        = (q : ℂ) * (z + (r : ℂ) * τ) + (q : ℂ) ^ 2 * τ by ring, jacobiTheta₂_add_left']
  rw [hterm, hθ]
  have key : Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((q : ℂ) * τ))
      * Complex.exp (-↑Real.pi * I * ((q : ℂ) ^ 2 * τ + 2 * ((q : ℂ) * (z + (r : ℂ) * τ))))
      = autFactor q 0 ((q : ℂ) * τ) z := by
    unfold autFactor; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← key]; ring

theorem Phi_mem {q : ℕ} (hq : 0 < q) (r : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Phi τ q r ∈ ThetaSpace q 0 ((q : ℂ) * τ) :=
  ⟨fun z => Phi_analyticAt hq r hτ z, fun z => Phi_add_one hq r hτ z,
    fun z => Phi_add_ptau hq r hτ z⟩

/-! ## Triangular jet orders -/

/-- **Target 1.** The `k`-th power of the atom `δ_b` has analytic order exactly `k` at `b`. -/
theorem deltaX_pow_order {T : ℂ} (hT : 0 < T.im) (b : ℂ) (k : ℕ) :
    analyticOrderAt (fun z => (deltaX T b z) ^ k) b = (k : ℕ∞) := by
  have hf : AnalyticAt ℂ (deltaX T b) b := deltaX_analyticAt hT b b
  have hpow : analyticOrderAt ((deltaX T b) ^ k) b = k • analyticOrderAt (deltaX T b) b :=
    analyticOrderAt_pow hf k
  have hfun : (fun z => (deltaX T b z) ^ k) = (deltaX T b) ^ k := by
    funext z; simp [Pi.pow_apply]
  rw [hfun, hpow, deltaX_simple_zero hT b]
  simp

/-- **Target 2.** Multiplying an order-`k` factor by an everywhere-analytic function that is
nonzero at the base point leaves the order unchanged. -/
theorem mul_order_of_ne_zero {b : ℂ} {g E : ℂ → ℂ} (k : ℕ)
    (hg : ∀ z, AnalyticAt ℂ g z) (hgb : g b ≠ 0)
    (hE : ∀ z, AnalyticAt ℂ E z) (hEord : analyticOrderAt E b = (k : ℕ∞)) :
    analyticOrderAt (fun z => E z * g z) b = (k : ℕ∞) := by
  have hfun : (fun z => E z * g z) = E * g := by funext z; rfl
  rw [hfun, analyticOrderAt_mul (hE b) (hg b), hEord,
    (hg b).analyticOrderAt_eq_zero.mpr hgb, add_zero]

/-- **Target 3.** Combining Targets 1 and 2: the product `δ_b^k · g` has analytic order exactly
`k` at `b`, when `g` is analytic everywhere and nonzero at `b`. -/
theorem deltaXpow_mul_order {T : ℂ} (hT : 0 < T.im) (b : ℂ) (k : ℕ) {g : ℂ → ℂ}
    (hg : ∀ z, AnalyticAt ℂ g z) (hgb : g b ≠ 0) :
    analyticOrderAt (fun z => (deltaX T b z) ^ k * g z) b = (k : ℕ∞) := by
  refine mul_order_of_ne_zero k hg hgb (fun z => (deltaX_analyticAt hT b z).pow k) ?_
  exact deltaX_pow_order hT b k

/-- **Target 4 (bonus).** Bridge from `analyticOrderAt (δ_b^k · g) b = k` to the vanishing of all
iterated derivatives of order `< k` at `b`. -/
theorem deltaXpow_mul_iteratedDeriv_eq_zero {T : ℂ} (hT : 0 < T.im) (b : ℂ) (k : ℕ) {g : ℂ → ℂ}
    (hg : ∀ z, AnalyticAt ℂ g z) (hgb : g b ≠ 0) :
    ∀ i < k, iteratedDeriv i (fun z => (deltaX T b z) ^ k * g z) b = 0 := by
  have hAt : AnalyticAt ℂ (fun z => (deltaX T b z) ^ k * g z) b :=
    ((deltaX_analyticAt hT b b).pow k).mul (hg b)
  have hle : (k : ℕ∞) ≤ analyticOrderAt (fun z => (deltaX T b z) ^ k * g z) b := by
    rw [deltaXpow_mul_order hT b k hg hgb]
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hAt).mp hle

/-! ## Translation-covariance of polynomialScaledDeriv -/

open LyubarskiiNes.TorsionJets

theorem scaledDeriv_comp_add (g : ℂ → ℂ) (c : ℂ) :
    scaledDeriv (fun z => g (z + c)) = fun x => scaledDeriv g (x + c) := by
  funext x
  unfold scaledDeriv
  rw [deriv_comp_add_const]

theorem iterScaledDeriv_comp_add (n : ℕ) (g : ℂ → ℂ) (c : ℂ) :
    iterScaledDeriv n (fun z => g (z + c)) = fun x => iterScaledDeriv n g (x + c) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show scaledDeriv (iterScaledDeriv k (fun z => g (z + c)))
      = fun x => scaledDeriv (iterScaledDeriv k g) (x + c)
    rw [ih, scaledDeriv_comp_add]

theorem polynomialScaledDeriv_comp_add (P : Polynomial ℂ) (g : ℂ → ℂ) (c x : ℂ) :
    polynomialScaledDeriv P (fun z => g (z + c)) x = polynomialScaledDeriv P g (x + c) := by
  unfold polynomialScaledDeriv
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [congrFun (iterScaledDeriv_comp_add n g c) x]

/-! ## 𝒯_0^0 = constants (rank 1) -/

/-! ## Finrank induction (dim 𝒯_N = N modulo base-case H1) -/

open scoped Real

/-! ## Probe: evaluation LinearMap and multiplication-by-δ LinearMap -/

/-- Evaluation-at-`z₀` as a `ℂ`-linear map out of `ThetaSpace (N+1) α T`. -/
noncomputable def evAt (N : ℕ) (α T z₀ : ℂ) : ThetaSpace (N+1) α T →ₗ[ℂ] ℂ where
  toFun f := (f : ℂ → ℂ) z₀
  map_add' f g := rfl
  map_smul' c f := rfl

/-- Multiplication by `δ_{z₀}` as a `ℂ`-linear map `𝒯_N(β) → 𝒯_{N+1}(α)`
with `β = α - (z₀ - 1/2 - T/2)`. -/
noncomputable def mulDelta {T : ℂ} (hT : 0 < T.im) (N : ℕ) (α z₀ : ℂ) :
    ThetaSpace N (α - (z₀ - 1/2 - T/2)) T →ₗ[ℂ] ThetaSpace (N+1) α T where
  toFun g := ⟨fun z => deltaX T z₀ z * (g : ℂ → ℂ) z, by
    have hd : deltaX T z₀ ∈ ThetaSpace 1 (z₀ - 1/2 - T/2) T := deltaX_mem_ThetaSpace hT z₀
    have hg : (g : ℂ → ℂ) ∈ ThetaSpace N (α - (z₀ - 1/2 - T/2)) T := g.2
    have hmul := ThetaSpace_mul hd hg
    rwa [show (1 + N) = (N + 1) by ring,
      show (z₀ - 1/2 - T/2) + (α - (z₀ - 1/2 - T/2)) = α by ring] at hmul⟩
  map_add' g₁ g₂ := by
    apply Subtype.ext; funext z
    show deltaX T z₀ z * ((g₁ : ℂ → ℂ) z + (g₂ : ℂ → ℂ) z)
      = deltaX T z₀ z * (g₁ : ℂ → ℂ) z + deltaX T z₀ z * (g₂ : ℂ → ℂ) z
    ring
  map_smul' c g := by
    apply Subtype.ext; funext z
    show deltaX T z₀ z * (c • (g : ℂ → ℂ)) z = c • (deltaX T z₀ z * (g : ℂ → ℂ) z)
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- `δ_{z₀}` vanishes at `z₀`. -/
theorem deltaX_self_zero {T : ℂ} (hT : 0 < T.im) (z₀ : ℂ) : deltaX T z₀ z₀ = 0 :=
  (deltaX_zero_iff hT z₀ z₀).mpr ⟨0, 0, by ring⟩

/-- `mulDelta` is injective. -/
theorem mulDelta_injective {T : ℂ} (hT : 0 < T.im) (N : ℕ) (α z₀ : ℂ) :
    Function.Injective (mulDelta hT N α z₀) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro g hg
  -- hg : mulDelta ... g = 0, i.e. (fun z => δ z * g z) = 0 as element of submodule
  have hzero : ∀ z, deltaX T z₀ z * (g : ℂ → ℂ) z = 0 := by
    intro z
    have h := congrArg (fun (f : ThetaSpace (N+1) α T) => (f : ℂ → ℂ) z) hg
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at h
    exact h
  have hga : ∀ z, AnalyticAt ℂ (g : ℂ → ℂ) z := g.2.1
  have := eq_zero_of_mul_deltaX hT hga (fun z => by rw [mul_comm]; exact hzero z)
  apply Subtype.ext; funext z; simpa using this z

/-- The range of `mulDelta` equals the kernel of evaluation at `z₀`. -/
theorem range_mulDelta_eq_ker {T : ℂ} (hT : 0 < T.im) (N : ℕ) (α z₀ : ℂ) :
    LinearMap.range (mulDelta hT N α z₀) = LinearMap.ker (evAt N α T z₀) := by
  apply le_antisymm
  · -- range ⊆ ker
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    show deltaX T z₀ z₀ * (g : ℂ → ℂ) z₀ = 0
    rw [deltaX_self_zero hT z₀, zero_mul]
  · -- ker ⊆ range
    intro f hf
    rw [LinearMap.mem_ker] at hf
    have hfz₀ : (f : ℂ → ℂ) z₀ = 0 := hf
    obtain ⟨g, hga, hfac, hgmem⟩ := deltaX_div hT f.2 hfz₀
    refine ⟨⟨g, hgmem⟩, ?_⟩
    apply Subtype.ext; funext z
    show deltaX T z₀ z * g z = (f : ℂ → ℂ) z
    exact (hfac z).symm

/-- `evAt` is surjective (given a section nonzero at `z₀`). -/
theorem evAt_surjective {T : ℂ} {N : ℕ} {α z₀ : ℂ}
    (f₀ : ThetaSpace (N+1) α T) (hf₀ : (f₀ : ℂ → ℂ) z₀ ≠ 0) :
    Function.Surjective (evAt N α T z₀) := by
  intro c
  refine ⟨(c / (f₀ : ℂ → ℂ) z₀) • f₀, ?_⟩
  show (c / (f₀ : ℂ → ℂ) z₀) • (f₀ : ℂ → ℂ) z₀ = c
  rw [smul_eq_mul, div_mul_cancel₀ _ hf₀]

/-- **Successor step, kernel side.** `ker (evAt z₀) ≃ₗ 𝒯_N(α-β)`, hence has `finrank = N`
whenever `finrank 𝒯_N = N`, and is finite-dimensional whenever `𝒯_N` is. -/
noncomputable def kerEvEquiv {T : ℂ} (hT : 0 < T.im) (N : ℕ) (α z₀ : ℂ) :
    ThetaSpace N (α - (z₀ - 1/2 - T/2)) T ≃ₗ[ℂ] LinearMap.ker (evAt N α T z₀) :=
  (LinearEquiv.ofInjective (mulDelta hT N α z₀) (mulDelta_injective hT N α z₀)).trans
    (LinearEquiv.ofEq _ _ (range_mulDelta_eq_ker hT N α z₀))

/-- **Successor step (rank form).**  Given `FiniteDimensional 𝒯_N(α')` and `finrank 𝒯_N(α') = N`
for every `α'`, plus a section of `𝒯_{N+1}(α)` nonzero at some point, we get
`Module.rank ℂ 𝒯_{N+1}(α) = N + 1`. -/
theorem rank_succ {T : ℂ} (hT : 0 < T.im) (N : ℕ) (α : ℂ)
    (ihFin : ∀ α' : ℂ, FiniteDimensional ℂ (ThetaSpace N α' T))
    (ihDim : ∀ α' : ℂ, Module.finrank ℂ (ThetaSpace N α' T) = N)
    {z₀ : ℂ} (f₀ : ThetaSpace (N+1) α T) (hf₀ : (f₀ : ℂ → ℂ) z₀ ≠ 0) :
    Module.rank ℂ (ThetaSpace (N+1) α T) = (N + 1 : ℕ) := by
  haveI : FiniteDimensional ℂ (ThetaSpace N (α - (z₀ - 1/2 - T/2)) T) := ihFin _
  -- rank of the kernel = N
  have hkerrank : Module.rank ℂ (LinearMap.ker (evAt N α T z₀)) = (N : ℕ) := by
    rw [← (kerEvEquiv hT N α z₀).rank_eq, ← Module.finrank_eq_rank ℂ, ihDim]
  -- range is everything of ℂ, rank 1
  have hsurj := evAt_surjective f₀ hf₀
  have hrangerank : Module.rank ℂ (LinearMap.range (evAt N α T z₀)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, rank_top, CommSemiring.rank_self ℂ]
  have hrn := LinearMap.rank_range_add_rank_ker (evAt N α T z₀)
  rw [hrangerank, hkerrank] at hrn
  rw [← hrn]
  push_cast; ring

/-- `evAt` is injective when no nonzero `𝒯_{N+1}` section vanishes at `z₀`. -/
theorem evAt_injective {T : ℂ} {N : ℕ} {α z₀ : ℂ}
    (hvanish : ∀ f : ThetaSpace (N+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0) :
    Function.Injective (evAt N α T z₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact hvanish f hf

/-- **Base case (rank form).**  If some section of `𝒯_1(α)` is nonzero at `z₀` and no nonzero
section of `𝒯_1(α)` vanishes at `z₀`, then `Module.rank ℂ 𝒯_1(α) = 1`. -/
theorem rank_one {T : ℂ} (α : ℂ) {z₀ : ℂ}
    (f₀ : ThetaSpace (0+1) α T) (hf₀ : (f₀ : ℂ → ℂ) z₀ ≠ 0)
    (hvanish : ∀ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0) :
    Module.rank ℂ (ThetaSpace (0+1) α T) = (1 : ℕ) := by
  have hbij : Function.Bijective (evAt 0 α T z₀) :=
    ⟨evAt_injective hvanish, evAt_surjective f₀ hf₀⟩
  have hequiv : ThetaSpace (0+1) α T ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective _ hbij
  rw [hequiv.rank_eq, CommSemiring.rank_self ℂ, Nat.cast_one]

/-- **Main dimension theorem (rank form), full induction.**
Given the degree-one vanishing input `H1` (for every character `α` there is a point `z₀` at which
some `𝒯_1(α)` section is nonzero and no nonzero `𝒯_1(α)` section vanishes), for every `N ≥ 1` and
every `α`, `Module.rank ℂ 𝒯_N(α) = N`. -/
theorem rank_thetaSpace {T : ℂ} (hT : 0 < T.im)
    (H1 : ∀ α : ℂ, ∃ z₀ : ℂ, (∃ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ ≠ 0) ∧
      (∀ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0))
    (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    Module.rank ℂ (ThetaSpace N α T) = (N : ℕ) := by
  induction N, hN using Nat.le_induction generalizing α with
  | base =>
    obtain ⟨z₀, ⟨f₀, hf₀⟩, hvanish⟩ := H1 α
    exact rank_one α f₀ hf₀ hvanish
  | succ N hN ih =>
    -- FiniteDimensional and finrank at level N, for all α', from the rank IH
    have ihFin : ∀ α' : ℂ, FiniteDimensional ℂ (ThetaSpace N α' T) := fun α' =>
      FiniteDimensional.of_rank_eq_nat (ih α')
    have ihDim : ∀ α' : ℂ, Module.finrank ℂ (ThetaSpace N α' T) = N := fun α' =>
      Module.finrank_eq_of_rank_eq (ih α')
    -- a section of 𝒯_{N+1}(α) nonzero at some z₀
    obtain ⟨f₀, hf₀mem, z₀, hz₀⟩ := ThetaSpace_exists_ne_zero hT (N+1) (Nat.le_add_left 1 N) α
    exact rank_succ hT N α ihFin ihDim ⟨f₀, hf₀mem⟩ hz₀

/-- **Main dimension theorem: `finrank ℂ 𝒯_N(α) = N` for `N ≥ 1`.** -/
theorem finrank_thetaSpace {T : ℂ} (hT : 0 < T.im)
    (H1 : ∀ α : ℂ, ∃ z₀ : ℂ, (∃ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ ≠ 0) ∧
      (∀ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0))
    (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    Module.finrank ℂ (ThetaSpace N α T) = N :=
  Module.finrank_eq_of_rank_eq (rank_thetaSpace hT H1 N hN α)

/-- **Finite-dimensionality of `𝒯_N(α)` for `N ≥ 1`.** -/
theorem finiteDimensional_thetaSpace {T : ℂ} (hT : 0 < T.im)
    (H1 : ∀ α : ℂ, ∃ z₀ : ℂ, (∃ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ ≠ 0) ∧
      (∀ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0))
    (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    FiniteDimensional ℂ (ThetaSpace N α T) :=
  FiniteDimensional.of_rank_eq_nat (rank_thetaSpace hT H1 N hN α)

/-! ## Exp-affine change-of-trivialization helpers (F4 conjuncts 1-3) -/

open scoped Real

theorem differentiable_iterScaledExpConjDeriv (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∀ n : ℕ, Differentiable ℂ (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) := by
  intro n
  induction n with
  | zero => simpa [LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv] using hg
  | succ n ih =>
    have hd : Differentiable ℂ (deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g)) :=
      analyticOnNhd_univ_iff_differentiable.mp
        (analyticOnNhd_univ_iff_differentiable.mpr ih).deriv
    have heq : LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A (n + 1) g
        = fun z => LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) z
          + (A * LyubarskiiNes.TorsionJets.paperDerivScale)
            * LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g z := by
      funext z; rfl
    rw [heq]
    exact (differentiable_const _ |>.mul hd).add ((differentiable_const _).mul ih)

/-- Every iterate of the plain normalized derivative `𝔡` of an entire function is entire. -/
theorem diff_iterScaledDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) := by
  induction k with
  | zero => exact hg
  | succ k ihk =>
    have hd : Differentiable ℂ (deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g)) :=
      analyticOnNhd_univ_iff_differentiable.mp (analyticOnNhd_univ_iff_differentiable.mpr ihk).deriv
    have heq : LyubarskiiNes.TorsionJets.iterScaledDeriv (k + 1) g
        = fun z => LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z := rfl
    rw [heq]; exact (differentiable_const _).mul hd

/-- The derivative of a finite `𝔡`-iterate combination distributes over the sum. -/
theorem deriv_sum_iterScaledDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    deriv (fun w => ∑ k ∈ Finset.range N, c k * LyubarskiiNes.TorsionJets.iterScaledDeriv k g w) z
      = ∑ k ∈ Finset.range N, c k * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z := by
  rw [deriv_fun_sum]
  · exact Finset.sum_congr rfl (fun k _ => by
      rw [deriv_const_mul _ ((diff_iterScaledDeriv hg k).differentiableAt)])
  · exact fun k _ => ((differentiable_const (c k)).mul (diff_iterScaledDeriv hg k)).differentiableAt

/-- Weighted Pascal recurrence used for the operator binomial theorem. -/
theorem weighted_pascal (F : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k : ℂ) * x^(n-k) * F (k+1))
    + (∑ k ∈ Finset.range (n+1), (n.choose k : ℂ) * x^(n+1-k) * F k)
    = ∑ k ∈ Finset.range (n+2), ((n+1).choose k : ℂ) * x^(n+1-k) * F k := by
  rw [Finset.sum_range_succ' (fun k => ((n+1).choose k : ℂ) * x^(n+1-k) * F k) (n+1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, pow_succ]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℂ) * x^(n+1-k) * F k) n]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.succ_sub_succ,
    Finset.sum_add_distrib, add_mul]
  rw [Finset.sum_range_succ (fun k => (n.choose (k+1) : ℂ) * x^(n-k) * F (k+1)) n, Nat.choose_succ_self]
  push_cast; ring

/-- **Operator binomial theorem.**  Because `𝔡` and the constant `A·s` commute, the exp-conjugated
iterate expands binomially: `(𝔡 + A·s)ⁿ g = ∑ₖ C(n,k)(A·s)^{n−k} 𝔡ᵏ g`.  This is the algebraic heart
of the Taylor-shift operator identity (F4 conjunct 3). -/
theorem iterScaledExpConjDeriv_binomial (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) :
    LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g
      = fun z => ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * (A * LyubarskiiNes.TorsionJets.paperDerivScale) ^ (n - k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z := by
  induction n with
  | zero => funext z; simp [LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv, LyubarskiiNes.TorsionJets.iterScaledDeriv]
  | succ n ih =>
    funext z
    have hstep : LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A (n + 1) g z
        = LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) z
          + (A * LyubarskiiNes.TorsionJets.paperDerivScale)
            * LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g z := rfl
    rw [hstep, ih, deriv_sum_iterScaledDeriv hg (n+1)
        (fun k => (n.choose k : ℂ) * (A * LyubarskiiNes.TorsionJets.paperDerivScale) ^ (n - k)) z,
        Finset.mul_sum, Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (n+1), LyubarskiiNes.TorsionJets.paperDerivScale
          * ((n.choose k : ℂ) * (A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z))
        = ∑ k ∈ Finset.range (n+1), (n.choose k : ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) g z from
      Finset.sum_congr rfl (fun k _ => by
        show _ = _ * _ * (LyubarskiiNes.TorsionJets.paperDerivScale
          * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z); ring)]
    rw [show (∑ k ∈ Finset.range (n+1), (A*LyubarskiiNes.TorsionJets.paperDerivScale)
          * ((n.choose k:ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z))
        = ∑ k ∈ Finset.range (n+1), (n.choose k:ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n+1-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z from
      Finset.sum_congr rfl (fun k hk => by
        have hkn : n - k + 1 = n + 1 - k := by rw [Finset.mem_range] at hk; omega
        rw [← hkn, pow_succ]; ring)]
    exact weighted_pascal (fun k => LyubarskiiNes.TorsionJets.iterScaledDeriv k g z)
      (A * LyubarskiiNes.TorsionJets.paperDerivScale) n

open Polynomial LyubarskiiNes.TorsionJets in
/-- **F4 conjunct 3: the Taylor-shift operator identity.**  Applying the polynomial `P` in the
exp-conjugated derivative `𝔡 + A·s` equals applying the Taylor-shifted polynomial `taylor (A·s) P` in
the plain derivative `𝔡`.  Both sides are linear in `P`; on monomials the identity is the operator
binomial theorem (`iterScaledExpConjDeriv_binomial`) matched against the Taylor coefficient of a
monomial (`hasseDeriv_monomial`).  This is the "remaining concrete identification" that
`torsion_jet_independence` consumes for `XiSection_changeOfTrivialization_data`. -/
theorem polynomialScaledExpConjDeriv_eq_taylor (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (P : Polynomial ℂ) :
    polynomialScaledExpConjDeriv A P g
      = polynomialScaledDeriv (taylor (A * paperDerivScale) P) g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    funext z
    have hL : polynomialScaledExpConjDeriv A (p + q) g z
        = polynomialScaledExpConjDeriv A p g z + polynomialScaledExpConjDeriv A q g z := by
      show (p + q).sum (fun n c => c * iterScaledExpConjDeriv A n g z) = _
      rw [Polynomial.sum_add_index]
      · rfl
      · intro n; ring
      · intro n a b; ring
    have hR : polynomialScaledDeriv (taylor (A * paperDerivScale) (p + q)) g z
        = polynomialScaledDeriv (taylor (A * paperDerivScale) p) g z
          + polynomialScaledDeriv (taylor (A * paperDerivScale) q) g z := by
      rw [map_add]
      show (taylor (A * paperDerivScale) p + taylor (A * paperDerivScale) q).sum
          (fun n c => c * iterScaledDeriv n g z) = _
      rw [Polynomial.sum_add_index]
      · rfl
      · intro n; ring
      · intro n a b; ring
    rw [hL, hR, congrFun hp z, congrFun hq z]
  | monomial n a =>
    funext z
    simp only [polynomialScaledExpConjDeriv_monomial]
    rw [congrFun (iterScaledExpConjDeriv_binomial A hg n) z, Finset.mul_sum]
    have hR : polynomialScaledDeriv (taylor (A * paperDerivScale) (monomial n a)) g z
        = ∑ k ∈ Finset.range (n+1),
            (n.choose k : ℂ) * a * (A * paperDerivScale)^(n-k) * iterScaledDeriv k g z := by
      show (taylor (A * paperDerivScale) (monomial n a)).sum
          (fun m c => c * iterScaledDeriv m g z) = _
      rw [Polynomial.sum_over_range' _ (fun m => by ring) (n+1) (by
        rw [polynomial_natDegree_taylor]
        exact Nat.lt_succ_of_le (Polynomial.natDegree_monomial_le a))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show (taylor (A * paperDerivScale) (monomial n a)).coeff k
          = (n.choose k : ℂ) * a * (A * paperDerivScale)^(n-k) from by
        rw [taylor_coeff, hasseDeriv_monomial, eval_monomial]]
    rw [hR]
    exact Finset.sum_congr rfl (fun k _ => by ring)

end LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
