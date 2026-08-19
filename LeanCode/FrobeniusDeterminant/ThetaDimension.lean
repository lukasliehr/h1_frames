import LeanCode.FrobeniusDeterminant.ResidueTheorem
import LeanCode.FrobeniusDeterminant.ThetaZeroCount
import LeanCode.FrobeniusDeterminant.ThetaFourierRegroup
import LeanCode.FrobeniusDeterminant.LevelPComponent
import LeanCode.TorsionJets.ExpConjugation
import LeanCode.ComplexAnalysis.DivisionByDivisor

/-!
# Theta-space dimension core (upstream of the skeleton)

This module is placed **upstream of `PrimitiveDerivativeSkeleton`** so that the analytic content
needed to discharge the skeleton's F3/F4 residuals is importable there.  It lifts (copies, to keep
the working `FrobeniusFactor` untouched) the two skeleton-independent blocks:

* the **argument-principle simple-zero** for `θ` (`theta_simple_zero`), built from `ResidueTheorem`
  and `ThetaZeroCount`;
* the **residue-jet machinery** (`iterScaledDeriv_fourier … Er_reduction`), built from `TorsionJets`
  and `ThetaFourierRegroup`.

On top of these it develops the `δ_x` atom and (subsequently) the theta-space dimension and
jet-surjectivity that both F3 (Abel) and F4 (jet independence) rest on, using the library's proven
`ComplexAnalysis.DivisionByDivisor.entire_div_pow_of_order_ge`.
-/

namespace LyubarskiiNes.FrobeniusDeterminant.ThetaDimension

open Matrix Complex
open scoped Real

/-- **Logarithmic derivative is periodic under `z ↦ z + 1`** (lifted, Mathlib-only). -/
theorem jacobiTheta₂_logDeriv_add_one (Ω z : ℂ) :
    jacobiTheta₂' (z + 1) Ω / jacobiTheta₂ (z + 1) Ω
      = jacobiTheta₂' z Ω / jacobiTheta₂ z Ω := by
  rw [jacobiTheta₂'_add_left, jacobiTheta₂_add_left]

/-- **Logarithmic derivative shift under `z ↦ z + Ω`** (lifted, Mathlib-only):
where `θ(z) ≠ 0`, `θ'/θ (z+Ω) = θ'/θ (z) − 2πi`. -/
theorem jacobiTheta₂_logDeriv_add_tau (Ω z : ℂ) (hz : jacobiTheta₂ z Ω ≠ 0) :
    jacobiTheta₂' (z + Ω) Ω / jacobiTheta₂ (z + Ω) Ω
      = jacobiTheta₂' z Ω / jacobiTheta₂ z Ω - 2 * (Real.pi : ℂ) * Complex.I := by
  rw [jacobiTheta₂'_add_left', jacobiTheta₂_add_left',
    mul_div_mul_left _ _ (Complex.exp_ne_zero _), sub_div, mul_div_assoc, div_self hz, mul_one]

/-- **`g = θ'/θ − m/(·−ζ)` (with the pole removed) is holomorphic on the cell neighbourhood.**
At the centre `ζ = (1+Ω)/2` the simple pole cancels (`differentiableAt_logDeriv_sub_extend`); elsewhere
`θ ≠ 0` (`theta_ne_zero_cellNbhd`) so it is `differentiableAt_logDeriv_sub_away`.  This is the
holomorphic integrand whose parallelogram Cauchy integral is `0`, completing `∮ θ'/θ = m·2πi`. -/
theorem differentiableOn_logDeriv_sub_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    DifferentiableOn ℂ
      (Function.update (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2))
        ((1 + Ω) / 2) (logDeriv u ((1 + Ω) / 2)))
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) := by
  intro z hz
  by_cases hzζ : z = (1 + Ω) / 2
  · subst hzζ
    exact (ResidueTheorem.differentiableAt_logDeriv_sub_extend hu hune hfac).differentiableWithinAt
  · have hθa : AnalyticAt ℂ (fun w => jacobiTheta₂ w Ω) z :=
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ z (Set.mem_univ z)
    have hθ0 : jacobiTheta₂ z Ω ≠ 0 :=
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_ne_zero_cellNbhd hΩ hz hzζ
    exact (ResidueTheorem.differentiableAt_logDeriv_sub_away hθa hθ0 hzζ).differentiableWithinAt

/-- The closed fundamental cell (base point `0`, sides `1` and `Ω`) lies in the open cell
neighbourhood — the containment `parContourIntegral_eq_zero_of_holo` consumes. -/
theorem cell_subset_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) (s t : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (0 : ℂ) + (s : ℂ) + (t : ℂ) * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω := by
  have hΩ0 : Ω.im ≠ 0 := ne_of_gt hΩ
  refine ⟨?_, ?_⟩
  · have h : ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).re
        - ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).im / Ω.im * Ω.re = s := by
      simp only [Complex.add_re, Complex.add_im, Complex.zero_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, zero_add, zero_mul, sub_zero, add_zero]
      field_simp; ring
    rw [h]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · have h : ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).im / Ω.im = t := by
      simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, zero_add, zero_mul, add_zero]
      field_simp
    rw [h]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **The four sides of the `ζ`-centered cell avoid the pole `ζ = (1+Ω)/2`.**  Bottom/top by imaginary
part (`0, Ω.im ≠ Ω.im/2`); right/left by forcing `t = 1/2` from the imaginary part, then a real-part
contradiction.  This lets `g` and its removable extension agree on the contour. -/
theorem sides_ne_zeta {Ω : ℂ} (hΩ : 0 < Ω.im) (t : ℝ) :
    (0:ℂ) + (t : ℂ) ≠ (1 + Ω)/2 ∧ (0:ℂ) + Ω + (t : ℂ) ≠ (1 + Ω)/2 ∧
    (0:ℂ) + 1 + (t : ℂ) * Ω ≠ (1 + Ω)/2 ∧ (0:ℂ) + (t : ℂ) * Ω ≠ (1 + Ω)/2 := by
  have hΩ0 : Ω.im ≠ 0 := ne_of_gt hΩ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.div_im, Complex.add_im,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, Complex.add_re,
      Complex.one_re, Complex.div_re, zero_add, zero_mul, add_zero, mul_zero] at this
    nlinarith [this, hΩ]
  · intro h; have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.div_im, Complex.add_im,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, Complex.add_re,
      Complex.one_re, Complex.div_re, zero_add, add_zero, mul_zero] at this
    nlinarith [this, hΩ]
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.div_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_re, Complex.one_re, Complex.div_re, zero_add, zero_mul,
      add_zero, mul_zero] at him
    have ht : t = 1/2 := mul_right_cancel₀ hΩ0 (by nlinarith [him] : t * Ω.im = 1/2 * Ω.im)
    subst ht
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.mul_im, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_im, Complex.one_im, Complex.div_im, zero_add, zero_mul,
      add_zero, sub_zero, mul_zero] at hre
    nlinarith [hre]
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.div_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_re, Complex.one_re, Complex.div_re, zero_add, zero_mul,
      add_zero, mul_zero] at him
    have ht : t = 1/2 := mul_right_cancel₀ hΩ0 (by nlinarith [him] : t * Ω.im = 1/2 * Ω.im)
    subst ht
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.mul_im, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_im, Complex.one_im, Complex.div_im, zero_add, zero_mul,
      add_zero, sub_zero, mul_zero] at hre
    nlinarith [hre]

/-- The four sides of the cell (as parametrised by `parContourIntegral`) lie in the cell
neighbourhood for `t ∈ [0,1]` — the continuity input the residue split's integrability needs. -/
theorem sides_mem_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    (0:ℂ) + ↑t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + 1 + ↑t * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + Ω + ↑t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + ↑t * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h11 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((0:ℂ) + ↑t) = 0 + ↑t + ↑(0:ℝ) * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ t 0 ht h01
  · rw [show ((0:ℂ) + 1 + ↑t * Ω) = 0 + ↑(1:ℝ) + ↑t * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ 1 t h11 ht
  · rw [show ((0:ℂ) + Ω + ↑t) = 0 + ↑t + ↑(1:ℝ) * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ t 1 ht h11
  · rw [show ((0:ℂ) + ↑t * Ω) = 0 + ↑(0:ℝ) + ↑t * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ 0 t h01 ht

/-- **Residue side, part 1: `∮_∂P (θ'/θ − m/(·−ζ)) = 0`.**  The integrand agrees on the contour with
its removable extension `g_ext` (they differ only at `ζ`, off the contour by `sides_ne_zeta`), and
`g_ext` is holomorphic on the whole cell, so the parallelogram Cauchy theorem gives `0`. -/
theorem theta_contour_g_zero {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    ResidueTheorem.parContourIntegral
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) 0 Ω = 0 := by
  set g : ℂ → ℂ := fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)
    with hg
  set gext := Function.update g ((1 + Ω) / 2) (logDeriv u ((1 + Ω) / 2)) with hgext
  have hgext0 : ResidueTheorem.parContourIntegral gext 0 Ω = 0 :=
    ResidueTheorem.parContourIntegral_eq_zero_of_holo _
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω)
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.isOpen_cellNbhd Ω)
      (differentiableOn_logDeriv_sub_cellNbhd hΩ hu hune hfac) 0 Ω
      (fun s t hs ht => by simpa using cell_subset_cellNbhd hΩ s t hs ht)
  have hupd : ∀ w : ℂ, w ≠ (1 + Ω) / 2 → g w = gext w :=
    fun w hw => (Function.update_of_ne hw _ g).symm
  have key : ResidueTheorem.parContourIntegral g 0 Ω = ResidueTheorem.parContourIntegral gext 0 Ω := by
    simp only [ResidueTheorem.parContourIntegral]
    rw [intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.2.2)]
  rw [key, hgext0]

/-- **Periodicity side of the argument principle for `θ`.**  `∮_∂P θ'/θ = 2πi` around the fundamental
cell (base `0`, sides `1` and `Ω`): the log-derivative has period `1` (`jacobiTheta₂_logDeriv_add_one`)
and a `−2πi` jump under `+Ω` (`jacobiTheta₂_logDeriv_add_tau`, valid since `θ` has no real zeros), and
`θ'/θ` is integrable on the real bottom side (θ non-vanishing there). -/
theorem theta_logDeriv_periodicity {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ResidueTheorem.parContourIntegral (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω
      = 2 * (Real.pi : ℂ) * I := by
  have hθan : AnalyticOnNhd ℂ (fun w => jacobiTheta₂ w Ω) Set.univ :=
    fun z _ => LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ z (Set.mem_univ z)
  have hθc : Continuous (fun w => jacobiTheta₂ w Ω) :=
    (analyticOnNhd_univ_iff_differentiable.mp hθan).continuous
  have hdθc : Continuous (deriv (fun w => jacobiTheta₂ w Ω)) :=
    (analyticOnNhd_univ_iff_differentiable.mp hθan.deriv).continuous
  refine ResidueTheorem.parContourIntegral_logDeriv_eq
    (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω ?_ ?_ ?_
  · intro t
    simp only [LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.logDeriv_jacobiTheta₂_eq hΩ]
    rw [show (0:ℂ) + 1 + (t:ℂ) * Ω = ((t:ℂ) * Ω) + 1 by ring,
      show (0:ℂ) + (t:ℂ) * Ω = (t:ℂ) * Ω by ring]
    exact jacobiTheta₂_logDeriv_add_one Ω ((t:ℂ) * Ω)
  · intro t
    simp only [LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.logDeriv_jacobiTheta₂_eq hΩ]
    rw [show (0:ℂ) + Ω + (t:ℂ) = (t:ℂ) + Ω by ring, show (0:ℂ) + (t:ℂ) = (t:ℂ) by ring]
    exact jacobiTheta₂_logDeriv_add_tau Ω (t:ℂ)
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_no_real_zero hΩ t)
  · apply ContinuousOn.intervalIntegrable
    have hcongr : (fun t : ℝ => logDeriv (fun w => jacobiTheta₂ w Ω) (0 + (t:ℂ)))
        = fun t : ℝ => deriv (fun w => jacobiTheta₂ w Ω) (0 + (t:ℂ)) / jacobiTheta₂ (0 + (t:ℂ)) Ω := by
      funext t; rw [logDeriv_apply]
    rw [hcongr]
    apply ContinuousOn.div ((hdθc.comp (by fun_prop)).continuousOn)
      ((hθc.comp (by fun_prop)).continuousOn)
    intro t _
    simp only [Function.comp_apply, zero_add]
    exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_no_real_zero hΩ t

/-- **Residue side of the argument principle: `∮_∂P θ'/θ = m·2πi`.**  Split `θ'/θ = m·(1/(·−ζ)) + g`,
where `g = θ'/θ − m/(·−ζ)` extends holomorphically across `ζ`.  The `g`-part integrates to `0`
(`theta_contour_g_zero`) and the pole part to `m·2πi` (winding number `parContourIntegral_inv_eq`). -/
theorem theta_contour_logDeriv_eq {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    ResidueTheorem.parContourIntegral (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω
      = (m : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  set gext := Function.update
    (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) ((1 + Ω) / 2)
    (logDeriv u ((1 + Ω) / 2)) with hgext
  have hgc : ContinuousOn gext (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) :=
    (differentiableOn_logDeriv_sub_cellNbhd hΩ hu hune hfac).continuousOn
  have hupd : ∀ w : ℂ, w ≠ (1 + Ω) / 2 →
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) w = gext w := by
    intro w hw; rw [hgext]
    exact (Function.update_of_ne hw (logDeriv u ((1 + Ω) / 2))
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2))).symm
  have gInt : ∀ (S : ℝ → ℂ), Continuous S →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ (1 + Ω) / 2) →
      IntervalIntegrable
        (fun t => logDeriv (fun w => jacobiTheta₂ w Ω) (S t) - (m : ℂ) / ((S t) - (1 + Ω) / 2))
        MeasureTheory.volume 0 1 := by
    intro S hS hmem hne
    apply ContinuousOn.intervalIntegrable
    exact (hgc.comp hS.continuousOn hmem).congr (fun t ht => hupd (S t) (hne t ht))
  have hInt : ∀ (S : ℝ → ℂ), Continuous S → (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ (1 + Ω) / 2) →
      IntervalIntegrable (fun t => (m : ℂ) * (1 / ((S t) - (1 + Ω) / 2))) MeasureTheory.volume 0 1 := by
    intro S hS hne
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      ((hS.sub continuous_const).continuousOn) (fun t ht => ?_))
    rw [sub_ne_zero]; exact hne t ht
  have heq : (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z)
      = fun z => (m : ℂ) * (1 / (z - (1 + Ω) / 2))
        + (logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) := by
    funext z; rw [mul_one_div]; ring
  rw [heq, ResidueTheorem.parContourIntegral_split (fun z => (m : ℂ) * (1 / (z - (1 + Ω) / 2)))
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) 0 Ω
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.2.2))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).1)
        (fun t _ => (sides_ne_zeta hΩ t).1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.1)
        (fun t _ => (sides_ne_zeta hΩ t).2.2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.2.1)
        (fun t _ => (sides_ne_zeta hΩ t).2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.2.2)
        (fun t _ => (sides_ne_zeta hΩ t).2.2.2))]
  rw [ResidueTheorem.parContourIntegral_const_mul, theta_contour_g_zero hΩ hu hune hfac, add_zero]
  rw [show ResidueTheorem.parContourIntegral (fun z => 1 / (z - (1 + Ω) / 2)) 0 Ω
      = 2 * (Real.pi : ℂ) * I from by
    simpa using ResidueTheorem.parContourIntegral_inv_eq ((1 + Ω) / 2) Ω hΩ]

/-- **The theta has a simple zero at `ζ = (1+Ω)/2`.**  Equating the two evaluations of the contour
integral `∮_∂P θ'/θ` — the residue side `m·2πi` and the periodicity side `2πi` — forces `m = 1`. -/
theorem theta_simple_zero {Ω : ℂ} (hΩ : 0 < Ω.im) :
    analyticOrderAt (fun w => jacobiTheta₂ w Ω) ((1 + Ω) / 2) = 1 := by
  obtain ⟨m, u, hm1, hu, hune, hfac⟩ := LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_order_factorization hΩ
  have hAt : AnalyticAt ℂ (fun w => jacobiTheta₂ w Ω) ((1 + Ω) / 2) :=
    LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ _ (Set.mem_univ _)
  have hm : (m : ℂ) * (2 * (Real.pi : ℂ) * I) = 2 * (Real.pi : ℂ) * I := by
    rw [← theta_contour_logDeriv_eq hΩ hu hune hfac, theta_logDeriv_periodicity hΩ]
  have h2πne : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hmc : (m : ℂ) = 1 := mul_right_cancel₀ h2πne (by rw [one_mul]; exact hm)
  have hmeq : m = 1 := by exact_mod_cast hmc
  rw [hAt.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hune, hfac⟩, hmeq, Nat.cast_one]

/-! ## Residue-jet machinery (lifted, skeleton-independent) -/

/-- The normalized operator `𝔡` commutes with multiplication by a constant. -/
theorem iterScaledDeriv_const_mul (C : ℂ) (f : ℂ → ℂ) (k : ℕ) :
    LyubarskiiNes.TorsionJets.iterScaledDeriv k (fun z => C * f z)
      = fun z => C * LyubarskiiNes.TorsionJets.iterScaledDeriv k f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    have h1 : LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) (fun z => C * f z) z
        = LyubarskiiNes.TorsionJets.paperDerivScale
          * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k (fun z => C * f z)) z := rfl
    have h2 : LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) f z
        = LyubarskiiNes.TorsionJets.paperDerivScale * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k f) z := rfl
    rw [h1, ih, h2, deriv_const_mul_field]; ring

/-- **`mᵏ`-weighted summability of the theta terms** — the tail bound `|m|ᵏ·e^{−π(Tm²−2S|m|)}` is
summable (`summable_pow_mul_jacobiTheta₂_term_bound`), so the `mᵏ`-weighted theta series converges. -/
theorem summable_intpow_theta_term {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) (k : ℕ) :
    Summable (fun n : ℤ => (n:ℂ)^k * jacobiTheta₂_term n z τ) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ k).of_norm_bounded ?_
  intro n; rw [norm_mul, norm_pow, Complex.norm_intCast, ← Int.cast_abs]; gcongr
  exact norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n

/-- **Finite character orthogonality:** for a frequency `m` not divisible by `q`,
`Σ_{s<q} e^{2πim·s/q} = 0` (geometric sum with primitive `q`-th root of unity). -/
theorem exp_orthogonality {q : ℕ} (hq : 0 < q) (m : ℤ) (hm : ¬ (q:ℤ) ∣ m) :
    ∑ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*((s:ℕ)/(q:ℂ))) = 0 := by
  have hq0 : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have h2πi : (2*(Real.pi:ℂ)*I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hpow : ∀ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*((s:ℕ)/(q:ℂ)))
      = (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^(s:ℕ) := by
    intro s; rw [← Complex.exp_nat_mul]; congr 1; field_simp
  rw [Finset.sum_congr rfl (fun s _ => hpow s), Fin.sum_univ_eq_sum_range
    (fun s => (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^s) q]
  rw [geom_sum_eq]
  · have hωq : (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^q = 1 := by
      rw [← Complex.exp_nat_mul,
        show (q:ℂ)*(2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) = (m:ℂ)*(2*(Real.pi:ℂ)*I) from by field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hωq]; simp
  · intro hω1
    apply hm
    rw [Complex.exp_eq_one_iff] at hω1
    obtain ⟨k, hk⟩ := hω1
    rw [div_eq_iff hq0] at hk
    have hmq : (m:ℂ) = (k:ℂ) * (q:ℂ) := mul_left_cancel₀ h2πi (by linear_combination hk)
    have hmk : m = k * q := by exact_mod_cast hmq
    exact ⟨k, by rw [hmk]; ring⟩

/-- **DFT inversion (step (ii) of the residue-jet obstruction):** if the DFT values
`Σ_r E_r·e^{2πir·s/q}` vanish for all `s : Fin q`, then every `E_r = 0`.  Multiply the `s`-th equation
by `e^{-2πir'·s/q}`, sum over `s`, and use character orthogonality (`exp_orthogonality`): the inner sum
is `q·δ_{r,r'}`, leaving `q·E_{r'} = 0`. -/
theorem dft_inversion {q : ℕ} (hq : 0 < q) (E : Fin q → ℂ)
    (hvan : ∀ s : Fin q, ∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))) = 0) :
    ∀ r' : Fin q, E r' = 0 := by
  intro r'
  have hinner : ∀ r : Fin q, (∑ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
      * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))))
      = if r = r' then (q:ℂ) else 0 := by
    intro r
    have hcomb : ∀ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
        * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ))))
        = Complex.exp (2*(Real.pi:ℂ)*I*(((r:ℤ)-(r':ℤ) : ℤ):ℂ)*((s:ℕ)/(q:ℂ))) := by
      intro s; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [Finset.sum_congr rfl (fun s _ => hcomb s)]
    by_cases hr : r = r'
    · subst hr; simp
    · rw [if_neg hr]
      apply exp_orthogonality hq
      intro hdvd
      have h1 : (r:ℕ) < q := r.isLt
      have h2 : (r':ℕ) < q := r'.isLt
      have h3 : (r:ℤ) - (r':ℤ) ≠ 0 := by intro h; apply hr; ext; omega
      have hle : (q:ℤ) ≤ |(r:ℤ) - (r':ℤ)| :=
        Int.le_of_dvd (abs_pos.mpr h3) ((dvd_abs _ _).mpr hdvd)
      have hlt : |(r:ℤ) - (r':ℤ)| < (q:ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
      linarith
  have key : ∑ r : Fin q, E r * (if r = r' then (q:ℂ) else 0)
      = ∑ s : Fin q, (∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))))
          * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))) := by
    simp_rw [Finset.sum_mul, ← hinner, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => by ring))
  have hzero : ∑ s : Fin q, (∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))))
          * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))) = 0 :=
    Finset.sum_eq_zero (fun s _ => by rw [hvan s, zero_mul])
  rw [hzero] at key
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  exact (mul_eq_zero.mp key).resolve_right (Nat.cast_ne_zero.mpr hq.ne')

/-- **The residue-`r` partial theta is a scaled theta of modulus `q²τ`:**
`Σ'_ℓ term_{qℓ+r}(w) = term_r(w) · θ(q(w+rτ), q²τ)`.  Each `(qℓ+r)²τ` splits as `r²τ + q²ℓ²τ + 2qℓrτ`,
so the sum over `ℓ` reindexes to `θ` at modulus `q²τ`.  Since `θ(·, q²τ)` has valence `1` and `term_r`
is nonvanishing, this exposes the valence structure the residue-jet independence (step (iii)) rests on. -/
theorem residue_partial_theta {q : ℕ} (hq : 0 < q) (r : ℤ) (w τ : ℂ) (hτ : 0 < τ.im) :
    ∑' ℓ : ℤ, jacobiTheta₂_term ((q:ℤ)*ℓ + r) w τ
      = jacobiTheta₂_term r w τ * jacobiTheta₂ ((q:ℂ)*(w + (r:ℂ)*τ)) ((q:ℂ)^2*τ) := by
  have hσ : 0 < ((q:ℂ)^2*τ).im := by
    rw [Complex.mul_im]
    have h1 : ((q:ℂ)^2).im = 0 := by
      rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring]; exact Complex.natCast_im _
    have h2 : ((q:ℂ)^2).re = (q:ℝ)^2 := by
      rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring, Complex.natCast_re]; push_cast; ring
    rw [h1, h2, zero_mul, add_zero]
    exact mul_pos (by positivity) hτ
  have hpt : ∀ ℓ : ℤ, jacobiTheta₂_term ((q:ℤ)*ℓ + r) w τ
      = jacobiTheta₂_term r w τ * jacobiTheta₂_term ℓ ((q:ℂ)*(w + (r:ℂ)*τ)) ((q:ℂ)^2*τ) := by
    intro ℓ; simp only [jacobiTheta₂_term]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [tsum_congr hpt, tsum_mul_left, (hasSum_jacobiTheta₂_term _ hσ).tsum_eq]

/-! ## Order helpers, θ lattice-order, and the `δ_x` atom -/

theorem analyticOrderAt_comp_add_const (f : ℂ → ℂ) (c z₀ : ℂ) :
    analyticOrderAt (fun z => f (z + c)) z₀ = analyticOrderAt f (z₀ + c) := by
  have hg : AnalyticAt ℂ (fun z : ℂ => z + c) z₀ := by fun_prop
  have hg' : deriv (fun z : ℂ => z + c) z₀ ≠ 0 := by rw [deriv_add_const, deriv_id'']; exact one_ne_zero
  simpa [Function.comp_def] using analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hg'
theorem analyticOrderAt_mul_left_nonzero {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) :
    analyticOrderAt (fun z => g z * f z) a = analyticOrderAt f a := by
  show analyticOrderAt (g * f) a = analyticOrderAt f a
  rw [analyticOrderAt_mul hg hf, hg.analyticOrderAt_eq_zero.mpr hga, zero_add]
theorem theta_analyticAt {Ω : ℂ} (hΩ : 0 < Ω.im) (w : ℂ) :
    AnalyticAt ℂ (fun z => jacobiTheta₂ z Ω) w :=
  LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ w (Set.mem_univ w)
theorem theta_order_add_tau {Ω : ℂ} (hΩ : 0 < Ω.im) (w : ℂ) :
    analyticOrderAt (fun z => jacobiTheta₂ z Ω) (w + Ω)
      = analyticOrderAt (fun z => jacobiTheta₂ z Ω) w := by
  have hA := analyticOrderAt_comp_add_const (fun z => jacobiTheta₂ z Ω) Ω w
  have heq : (fun z => jacobiTheta₂ (z + Ω) Ω)
      = (fun z => Complex.exp (-↑Real.pi * I * (Ω + 2*z)) * jacobiTheta₂ z Ω) := by
    funext z; exact jacobiTheta₂_add_left' z Ω
  rw [heq] at hA; rw [← hA]
  exact analyticOrderAt_mul_left_nonzero (theta_analyticAt hΩ w) (by fun_prop) (Complex.exp_ne_zero _)
theorem theta_order_add_intMul_tau {Ω : ℂ} (hΩ : 0 < Ω.im) (w : ℂ) (n : ℤ) :
    analyticOrderAt (fun z => jacobiTheta₂ z Ω) (w + n * Ω)
      = analyticOrderAt (fun z => jacobiTheta₂ z Ω) w := by
  set F := fun z => jacobiTheta₂ z Ω with hF
  refine Int.induction_on n ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · have hstep : analyticOrderAt F ((w + ((k:ℤ):ℂ) * Ω) + Ω) = analyticOrderAt F (w + ((k:ℤ):ℂ) * Ω) := by
      rw [hF]; exact theta_order_add_tau hΩ _
    calc analyticOrderAt F (w + ((k:ℤ)+1 : ℤ) * Ω)
        = analyticOrderAt F ((w + ((k:ℤ):ℂ) * Ω) + Ω) := congrArg (analyticOrderAt F) (by push_cast; ring)
      _ = analyticOrderAt F (w + ((k:ℤ):ℂ) * Ω) := hstep
      _ = analyticOrderAt F w := ih
  · have hstep : analyticOrderAt F ((w + (-((k:ℤ)+1):ℂ) * Ω) + Ω) = analyticOrderAt F (w + (-((k:ℤ)+1):ℂ) * Ω) := by
      rw [hF]; exact theta_order_add_tau hΩ _
    calc analyticOrderAt F (w + (-(k:ℤ)-1 : ℤ) * Ω)
        = analyticOrderAt F (w + (-((k:ℤ)+1):ℂ) * Ω) := congrArg (analyticOrderAt F) (by push_cast; ring)
      _ = analyticOrderAt F ((w + (-((k:ℤ)+1):ℂ) * Ω) + Ω) := hstep.symm
      _ = analyticOrderAt F (w + ((-(k:ℤ) : ℤ):ℂ) * Ω) := congrArg (analyticOrderAt F) (by push_cast; ring)
      _ = analyticOrderAt F w := ih

theorem theta_order_at_lattice {Ω : ℂ} (hΩ : 0 < Ω.im) (m n : ℤ) :
    analyticOrderAt (fun z => jacobiTheta₂ z Ω) ((1+Ω)/2 + m + n * Ω) = 1 := by
  rw [show (1+Ω)/2 + (m:ℂ) + (n:ℂ)*Ω = ((1+Ω)/2 + (n:ℂ)*Ω) + (m:ℂ) by ring]
  have h1 := analyticOrderAt_comp_add_const (fun z => jacobiTheta₂ z Ω) ((m:ℤ):ℂ) ((1+Ω)/2 + (n:ℂ)*Ω)
  have heq : (fun z => jacobiTheta₂ (z + ((m:ℤ):ℂ)) Ω) = (fun z => jacobiTheta₂ z Ω) := by
    funext z; exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_add_intCast Ω z m
  rw [heq] at h1
  rw [← h1, theta_order_add_intMul_tau hΩ, theta_simple_zero hΩ]

/-- The `δ_x` atom `δ_x(z) = θ(z - x + (1+T)/2; T)`. -/
noncomputable def deltaX (T x : ℂ) : ℂ → ℂ := fun z => jacobiTheta₂ (z - x + (1+T)/2) T

theorem deltaX_analyticAt {T : ℂ} (hT : 0 < T.im) (x w : ℂ) :
    AnalyticAt ℂ (deltaX T x) w := by
  have : deltaX T x = (fun z => jacobiTheta₂ z T) ∘ (fun z => z + ((1+T)/2 - x)) := by
    funext z; simp only [deltaX, Function.comp_apply]; ring_nf
  rw [this]
  exact (theta_analyticAt hT _).comp (by fun_prop)

theorem deltaX_zero_iff {T : ℂ} (hT : 0 < T.im) (x z : ℂ) :
    deltaX T x z = 0 ↔ ∃ m n : ℤ, z = x + m + n * T := by
  unfold deltaX
  constructor
  · intro h
    obtain ⟨m, n, hmn⟩ := LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_mem_of_eq_zero hT _ h
    exact ⟨m, n, by rw [← sub_eq_iff_eq_add] at hmn ⊢; linear_combination hmn⟩
  · rintro ⟨m, n, rfl⟩
    have : x + (m:ℂ) + (n:ℂ) * T - x + (1+T)/2 = (1+T)/2 + (m:ℂ) + (n:ℂ)*T := by ring
    rw [this]; exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_eq_zero_at_lattice T m n

theorem deltaX_simple_zero {T : ℂ} (hT : 0 < T.im) (x : ℂ) :
    analyticOrderAt (deltaX T x) x = 1 := by
  have : deltaX T x = (fun z => jacobiTheta₂ z T) ∘ (fun z => z + ((1+T)/2 - x)) := by
    funext z; simp only [deltaX, Function.comp_apply]; ring_nf
  rw [this]
  have h1 := analyticOrderAt_comp_add_const (fun z => jacobiTheta₂ z T) ((1+T)/2 - x) x
  rw [show x + ((1+T)/2 - x) = (1+T)/2 by ring, theta_simple_zero hT] at h1
  rw [show ((fun z => jacobiTheta₂ z T) ∘ fun z => z + ((1+T)/2 - x))
      = (fun z => jacobiTheta₂ (z + ((1+T)/2 - x)) T) from rfl]
  exact h1

theorem deltaX_order_at_lattice {T : ℂ} (hT : 0 < T.im) (x : ℂ) (m n : ℤ) :
    analyticOrderAt (deltaX T x) (x + m + n * T) = 1 := by
  have hcomp : deltaX T x = (fun z => jacobiTheta₂ (z + ((1+T)/2 - x)) T) := by
    funext z; simp only [deltaX]; ring_nf
  rw [hcomp]
  have h1 := analyticOrderAt_comp_add_const (fun z => jacobiTheta₂ z T) ((1+T)/2 - x) (x + m + n*T)
  rw [show (x + (m:ℂ) + (n:ℂ)*T) + ((1+T)/2 - x) = (1+T)/2 + (m:ℂ) + (n:ℂ)*T by ring,
    theta_order_at_lattice hT] at h1
  exact h1

theorem deltaX_add_one (T x z : ℂ) : deltaX T x (z + 1) = deltaX T x z := by
  simp only [deltaX]
  rw [show z + 1 - x + (1+T)/2 = (z - x + (1+T)/2) + 1 by ring, jacobiTheta₂_add_left]

theorem deltaX_add_tau (T x z : ℂ) :
    deltaX T x (z + T)
      = Complex.exp (-(Real.pi:ℂ)*I*(T + 2*(z - x + (1+T)/2))) * deltaX T x z := by
  simp only [deltaX]
  rw [show z + T - x + (1+T)/2 = (z - x + (1+T)/2) + T by ring, jacobiTheta₂_add_left']

/-! ## The theta space `𝒯_N^α(T)` as a submodule -/

/-- Automorphy factor of `𝒯_N^α(T)`: `e^{-πiNT - 2πiNz + 2πiα}`. -/
noncomputable def autFactor (N : ℕ) (α T z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*I*(N:ℂ)*T - 2*(Real.pi:ℂ)*I*(N:ℂ)*z + 2*(Real.pi:ℂ)*I*α)

theorem autFactor_ne_zero (N : ℕ) (α T z : ℂ) : autFactor N α T z ≠ 0 := Complex.exp_ne_zero _

/-- The theta space `𝒯_N^α(T)` as a `ℂ`-submodule of entire functions. -/
noncomputable def ThetaSpace (N : ℕ) (α T : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | (∀ z, AnalyticAt ℂ f z) ∧ (∀ z, f (z + 1) = f z) ∧
    (∀ z, f (z + T) = autFactor N α T z * f z)}
  zero_mem' := by
    refine ⟨fun z => analyticAt_const, fun z => rfl, fun z => ?_⟩
    simp
  add_mem' := by
    rintro f g ⟨hfa, hf1, hfT⟩ ⟨hga, hg1, hgT⟩
    refine ⟨fun z => (hfa z).add (hga z), fun z => ?_, fun z => ?_⟩
    · simp only [Pi.add_apply]; rw [hf1, hg1]
    · simp only [Pi.add_apply]; rw [hfT, hgT]; ring
  smul_mem' := by
    rintro c f ⟨hfa, hf1, hfT⟩
    refine ⟨fun z => (analyticAt_const).mul (hfa z), fun z => ?_, fun z => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [hf1]
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [hfT]; ring

/-- `δ_x ∈ 𝒯_1^{β_x}(T)` with `β_x = x - 1/2 - T/2`. -/
theorem deltaX_mem_ThetaSpace {T : ℂ} (hT : 0 < T.im) (x : ℂ) :
    deltaX T x ∈ ThetaSpace 1 (x - 1/2 - T/2) T := by
  refine ⟨fun z => deltaX_analyticAt hT x z, deltaX_add_one T x, fun z => ?_⟩
  rw [deltaX_add_tau]
  congr 1
  unfold autFactor
  push_cast
  ring_nf

/-! ## δ-division isomorphism (kernel of the evaluation map) -/

theorem analyticAt_shift {g : ℂ → ℂ} (hg : ∀ z, AnalyticAt ℂ g z) (c z : ℂ) :
    AnalyticAt ℂ (fun w => g (w + c)) z := by
  have h : (fun w => g (w + c)) = g ∘ (fun w : ℂ => w + c) := rfl
  rw [h]
  exact AnalyticAt.comp_of_eq (hg (z + c))
    (show AnalyticAt ℂ (fun w : ℂ => w + c) z from by fun_prop) rfl

theorem eq_zero_of_mul_deltaX {T x : ℂ} (hT : 0 < T.im) {h : ℂ → ℂ}
    (hh : ∀ z, AnalyticAt ℂ h z) (hmul : ∀ z, h z * deltaX T x z = 0) : ∀ z, h z = 0 := by
  obtain ⟨z₀, hz₀⟩ := LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_ne_zero_somewhere hT
  have hdw : deltaX T x (z₀ + x - (1+T)/2) ≠ 0 := by
    simp only [deltaX]
    rw [show z₀ + x - (1+T)/2 - x + (1+T)/2 = z₀ by ring]; exact hz₀
  have hh0 : h =ᶠ[nhds (z₀ + x - (1+T)/2)] 0 := by
    filter_upwards [(deltaX_analyticAt hT x _).continuousAt.eventually_ne hdw] with z hz
    exact (mul_eq_zero.mp (hmul z)).resolve_right hz
  have hAOn : AnalyticOnNhd ℂ h Set.univ := fun w _ => hh w
  intro z
  exact hAOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hh0 (Set.mem_univ z)

theorem ThetaSpace_zero_add_int {N : ℕ} {α T : ℂ} {f : ℂ → ℂ} (hf : f ∈ ThetaSpace N α T)
    {z₀ : ℂ} (hz : f z₀ = 0) (m : ℤ) : f (z₀ + m) = 0 := by
  have h1 := hf.2.1
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simpa using hz
  · calc f (z₀ + ((k:ℤ)+1 : ℤ)) = f ((z₀ + ((k:ℤ):ℂ)) + 1) := congrArg f (by push_cast; ring)
      _ = f (z₀ + ((k:ℤ):ℂ)) := h1 _
      _ = 0 := ih
  · calc f (z₀ + (-(k:ℤ)-1 : ℤ)) = f ((z₀ + (-((k:ℤ)+1):ℂ)) ) := congrArg f (by push_cast; ring)
      _ = f ((z₀ + (-((k:ℤ)+1):ℂ)) + 1) := (h1 _).symm
      _ = f (z₀ + ((-(k:ℤ) : ℤ):ℂ)) := congrArg f (by push_cast; ring)
      _ = 0 := ih

theorem ThetaSpace_zero_lattice {N : ℕ} {α T : ℂ} {f : ℂ → ℂ} (hf : f ∈ ThetaSpace N α T)
    {z₀ : ℂ} (hz : f z₀ = 0) (m n : ℤ) : f (z₀ + m + n * T) = 0 := by
  have hTa := hf.2.2
  have base : ∀ k : ℤ, f (z₀ + (m:ℂ) + k) = 0 := fun k =>
    ThetaSpace_zero_add_int hf (ThetaSpace_zero_add_int hf hz m) k
  refine Int.induction_on n ?_ (fun k ih => ?_) (fun k ih => ?_)
  · have := base 0; simpa using this
  · calc f (z₀ + (m:ℂ) + ((k:ℤ)+1 : ℤ) * T)
        = f ((z₀ + (m:ℂ) + ((k:ℤ):ℂ)*T) + T) := congrArg f (by push_cast; ring)
      _ = autFactor N α T (z₀ + (m:ℂ) + ((k:ℤ):ℂ)*T) * f (z₀ + (m:ℂ) + ((k:ℤ):ℂ)*T) := hTa _
      _ = 0 := by rw [ih, mul_zero]
  · have hstep := hTa (z₀ + (m:ℂ) + (-((k:ℤ)+1):ℂ)*T)
    rw [show (z₀ + (m:ℂ) + (-((k:ℤ)+1):ℂ)*T) + T = z₀ + (m:ℂ) + ((-(k:ℤ) : ℤ):ℂ)*T by push_cast; ring,
      ih] at hstep
    have hfP : f (z₀ + (m:ℂ) + (-((k:ℤ)+1):ℂ)*T) = 0 :=
      (mul_eq_zero.mp hstep.symm).resolve_left (autFactor_ne_zero _ _ _ _)
    calc f (z₀ + (m:ℂ) + (-(k:ℤ)-1 : ℤ) * T)
        = f (z₀ + (m:ℂ) + (-((k:ℤ)+1):ℂ)*T) := congrArg f (by push_cast; ring)
      _ = 0 := hfP

/-- Product identity for automorphy factors: `aut_1^β · aut_N^{α-β} = aut_{N+1}^α`. -/
theorem autFactor_mul (N : ℕ) (α β T z : ℂ) :
    autFactor 1 β T z * autFactor N (α - β) T z = autFactor (N+1) α T z := by
  unfold autFactor
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem autFactor_analyticAt (N : ℕ) (α T z : ℂ) :
    AnalyticAt ℂ (fun w => autFactor N α T w) z := by
  unfold autFactor; fun_prop

/-- **δ-division isomorphism.**  If `f ∈ 𝒯_{N+1}^α(T)` vanishes at `z₀`, then `f = δ_{z₀}·g` with
`g ∈ 𝒯_N^{α-β}(T)`, `β = z₀ - 1/2 - T/2`. -/
theorem deltaX_div {N : ℕ} {α T : ℂ} (hT : 0 < T.im) {f : ℂ → ℂ}
    (hf : f ∈ ThetaSpace (N+1) α T) {z₀ : ℂ} (hz : f z₀ = 0) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ (∀ z, f z = deltaX T z₀ z * g z) ∧
      g ∈ ThetaSpace N (α - (z₀ - 1/2 - T/2)) T := by
  set D : Set ℂ := {z | ∃ m n : ℤ, z = z₀ + (m:ℂ) + (n:ℂ) * T} with hD
  have hzero : ∀ z, deltaX T z₀ z = 0 ↔ z ∈ D := fun z => deltaX_zero_iff hT z₀ z
  have hsimple : ∀ z ∈ D, analyticOrderAt (deltaX T z₀) z = (1:ℕ∞) := by
    rintro z ⟨m, n, rfl⟩; exact deltaX_order_at_lattice hT z₀ m n
  have hvan : ∀ z ∈ D, f z = 0 := by
    rintro z ⟨m, n, rfl⟩; exact ThetaSpace_zero_lattice hf hz m n
  have hForder : ∀ z ∈ D, (1:ℕ∞) ≤ analyticOrderAt f z := by
    intro z hzD
    rw [Order.one_le_iff_ne_zero]
    exact fun h => (hf.1 z).analyticOrderAt_eq_zero.mp h (hvan z hzD)
  obtain ⟨g, hga, hgeq⟩ := LyubarskiiNes.ComplexAnalysis.entire_div_pow_of_order_ge
    (D := D) (E := deltaX T z₀) (F := f) (k := 1)
    (fun z => deltaX_analyticAt hT z₀ z) (fun z => hf.1 z) hzero hsimple hForder
  have hfactor : ∀ z, f z = deltaX T z₀ z * g z := by
    intro z
    by_cases hzD : z ∈ D
    · rw [hvan z hzD, (hzero z).mpr hzD, zero_mul]
    · have hne : deltaX T z₀ z ≠ 0 := fun h => hzD ((hzero z).mp h)
      rw [hgeq z hzD, pow_one, mul_div_cancel₀ _ hne]
  have hg1 : ∀ z, g (z + 1) = g z := by
    have hcancel : ∀ z, (fun w => g (w+1) - g w) z * deltaX T z₀ z = 0 := by
      intro z
      show (g (z+1) - g z) * deltaX T z₀ z = 0
      have e1 : deltaX T z₀ z * g (z + 1) = f (z+1) := by rw [hfactor (z+1), deltaX_add_one]
      have key : deltaX T z₀ z * g (z+1) = deltaX T z₀ z * g z := by
        rw [e1, hf.2.1 z]; exact hfactor z
      linear_combination key
    have hz := eq_zero_of_mul_deltaX hT
      (fun z => (analyticAt_shift hga 1 z).sub (hga z)) hcancel
    intro z; have h : g (z+1) - g z = 0 := hz z; exact sub_eq_zero.mp h
  have hgT : ∀ z, g (z + T) = autFactor N (α - (z₀ - 1/2 - T/2)) T z * g z := by
    set β := z₀ - 1/2 - T/2 with hβ
    have hdmem := deltaX_mem_ThetaSpace hT z₀
    have hcancel : ∀ z, (fun w => autFactor 1 β T w * g (w+T) - autFactor (N+1) α T w * g w) z
        * deltaX T z₀ z = 0 := by
      intro z
      show (autFactor 1 β T z * g (z+T) - autFactor (N+1) α T z * g z) * deltaX T z₀ z = 0
      have e1 : f (z+T) = autFactor 1 β T z * deltaX T z₀ z * g (z+T) := by
        rw [hfactor (z+T), hdmem.2.2 z]
      have e2 : f (z+T) = autFactor (N+1) α T z * deltaX T z₀ z * g z := by
        rw [hf.2.2 z, hfactor z]; ring
      have key : autFactor 1 β T z * deltaX T z₀ z * g (z+T)
          = autFactor (N+1) α T z * deltaX T z₀ z * g z := by rw [← e1, e2]
      linear_combination key
    have hz := eq_zero_of_mul_deltaX hT
      (fun z => ((autFactor_analyticAt 1 β T z).mul (analyticAt_shift hga T z)).sub
        ((autFactor_analyticAt (N+1) α T z).mul (hga z))) hcancel
    intro z
    have heq : autFactor 1 β T z * g (z+T) = autFactor (N+1) α T z * g z := sub_eq_zero.mp (hz z)
    rw [← autFactor_mul N α β T z, mul_assoc] at heq
    exact mul_left_cancel₀ (autFactor_ne_zero 1 β T z) heq
  exact ⟨g, hga, hfactor, hga, hg1, hgT⟩

/-! ## Products, cancellation, and existence of nonzero elements -/

/-- Additive law for automorphy factors under products. -/
theorem autFactor_add (N₁ N₂ : ℕ) (α₁ α₂ T z : ℂ) :
    autFactor N₁ α₁ T z * autFactor N₂ α₂ T z = autFactor (N₁+N₂) (α₁+α₂) T z := by
  unfold autFactor; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Product of theta-space elements: `𝒯_{N₁}^{α₁} · 𝒯_{N₂}^{α₂} ⊆ 𝒯_{N₁+N₂}^{α₁+α₂}`. -/
theorem ThetaSpace_mul {N₁ N₂ : ℕ} {α₁ α₂ T : ℂ} {f₁ f₂ : ℂ → ℂ}
    (h₁ : f₁ ∈ ThetaSpace N₁ α₁ T) (h₂ : f₂ ∈ ThetaSpace N₂ α₂ T) :
    (fun z => f₁ z * f₂ z) ∈ ThetaSpace (N₁+N₂) (α₁+α₂) T := by
  refine ⟨fun z => (h₁.1 z).mul (h₂.1 z), fun z => ?_, fun z => ?_⟩
  · simp only; rw [h₁.2.1, h₂.2.1]
  · simp only [h₁.2.2, h₂.2.2]; rw [← autFactor_add]; ring

/-- **General entire cancellation:** if `f·g ≡ 0` with `f, g` entire and `f ≢ 0`, then `g ≡ 0`. -/
theorem entire_eq_zero_of_mul {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (hne : ∃ w, f w ≠ 0) (hmul : ∀ z, f z * g z = 0) : ∀ z, g z = 0 := by
  obtain ⟨w, hw⟩ := hne
  have hg0 : g =ᶠ[nhds w] 0 := by
    filter_upwards [(hf w).continuousAt.eventually_ne hw] with z hz
    exact (mul_eq_zero.mp (hmul z)).resolve_left hz
  have hAOn : AnalyticOnNhd ℂ g Set.univ := fun u _ => hg u
  intro z
  exact hAOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hg0 (Set.mem_univ z)

/-- `δ_x ≢ 0`. -/
theorem deltaX_ne_zero_fun {T : ℂ} (hT : 0 < T.im) (x : ℂ) : ∃ z, deltaX T x z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_ne_zero_somewhere hT
  refine ⟨z₀ + x - (1+T)/2, ?_⟩
  simp only [deltaX]; rw [show z₀ + x - (1+T)/2 - x + (1+T)/2 = z₀ by ring]; exact hz₀

/-- A nonzero entire function times `δ_x` is nonzero somewhere. -/
theorem mul_deltaX_ne_zero {T : ℂ} (hT : 0 < T.im) {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hfne : ∃ w, f w ≠ 0) (x : ℂ) :
    ∃ z, f z * deltaX T x z ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨w, hw⟩ := hfne
  exact hw (entire_eq_zero_of_mul (fun z => deltaX_analyticAt hT x z) hf
    (deltaX_ne_zero_fun hT x) (fun z => by rw [mul_comm]; exact h z) w)

set_option maxHeartbeats 400000 in
theorem ThetaSpace_exists_ne_zero {T : ℂ} (hT : 0 < T.im) (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    ∃ f : ℂ → ℂ, f ∈ ThetaSpace N α T ∧ ∃ z, f z ≠ 0 := by
  induction N, hN using Nat.le_induction generalizing α with
  | base =>
    refine ⟨deltaX T (α + (1+T)/2), ?_, deltaX_ne_zero_fun hT _⟩
    have h := deltaX_mem_ThetaSpace hT (α + (1+T)/2)
    rwa [show α + (1+T)/2 - 1/2 - T/2 = α by ring] at h
  | succ N hN ih =>
    obtain ⟨g, hg, hgne⟩ := ih α
    have hθ : deltaX T ((1+T)/2) ∈ ThetaSpace 1 0 T := by
      have h := deltaX_mem_ThetaSpace hT ((1+T)/2)
      rwa [show (1+T)/2 - 1/2 - T/2 = 0 by ring] at h
    have hmem : (fun z => deltaX T ((1+T)/2) z * g z) ∈ ThetaSpace (N+1) α T := by
      refine ⟨fun z => (deltaX_analyticAt hT _ z).mul (hg.1 z), fun z => ?_, fun z => ?_⟩
      · show deltaX T ((1+T)/2) (z+1) * g (z+1) = deltaX T ((1+T)/2) z * g z
        rw [deltaX_add_one, hg.2.1]
      · show deltaX T ((1+T)/2) (z+T) * g (z+T) = autFactor (N+1) α T z * (deltaX T ((1+T)/2) z * g z)
        have hae : autFactor 1 0 T z * autFactor N α T z = autFactor (N+1) α T z := by
          unfold autFactor; rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hθ.2.2 z, hg.2.2 z, mul_mul_mul_comm, hae]
    obtain ⟨z, hz⟩ := mul_deltaX_ne_zero hT hg.1 hgne ((1+T)/2)
    exact ⟨_, hmem, z, by rw [mul_comm]; exact hz⟩

/-! ## Elliptic Liouville / one-pole classification (lifted from FrobeniusFactor, ResidueTheorem-only) -/

theorem const_of_entire_doubly_periodic (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {c : ℂ} (hc : 0 < c.im) (h1 : Function.Periodic f 1) (hcp : Function.Periodic f c) :
    ∃ C : ℂ, ∀ z : ℂ, f z = C := by
  set K : Set ℂ :=
    (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 • c) '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) with hKdef
  have hKcomp : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hsurj : ∀ z : ℂ, ∃ k ∈ K, f z = f k := by
    intro z
    set b : ℝ := z.im / c.im with hb
    set a : ℝ := z.re - b * c.re with ha
    have hz : z = (a : ℂ) + b • c := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.smul_re, smul_eq_mul, ha]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, smul_eq_mul, zero_add, hb]
        field_simp
    have hmem : ((Int.fract a, Int.fract b) : ℝ × ℝ)
        ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩
        ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩
    have hkK : ((Int.fract a : ℝ) : ℂ) + (Int.fract b : ℝ) • c ∈ K :=
      hKdef ▸ ⟨(Int.fract a, Int.fract b), hmem, rfl⟩
    refine ⟨((Int.fract a : ℝ) : ℂ) + (Int.fract b : ℝ) • c, hkK, ?_⟩
    rw [hz, ← h1.sub_int_mul_eq ⌊a⌋ (x := (a : ℂ) + b • c),
      ← hcp.sub_int_mul_eq ⌊b⌋ (x := (a : ℂ) + b • c - (⌊a⌋ : ℂ) * 1)]
    congr 1
    simp only [Int.fract, Complex.real_smul]
    push_cast
    ring
  have hbound : Bornology.IsBounded (Set.range f) := by
    have hsub : Set.range f ⊆ f '' K := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨k, hk, hfk⟩ := hsurj z
      exact ⟨k, hk, hfk.symm⟩
    exact ((hKcomp.image hf.continuous).isBounded).subset hsub
  obtain ⟨C, hC⟩ := hf.exists_eq_const_of_bounded hbound
  exact ⟨C, fun z => congrFun hC z⟩

/-! ## cellNbhd geometry (convexity + lattice cover) -/

open LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount in
section
open LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount

end

/-! ## Base case dim 𝒯_1 = 1: removable singularity of the ratio f/δ -/

open Topology Filter in
-- The ratio f/δ minus its principal part extends analytically at the simple zero ζ of δ.
-- Model: δ =ᶠ (z-ζ)·u near ζ, u ζ ≠ 0.  Then f/δ - r/(z-ζ) =ᶠ dslope (f/u) ζ  (r = f ζ / u ζ).
theorem differentiableAt_ratio_sub_extend {f δ u : ℂ → ℂ} {ζ : ℂ}
    (hf : AnalyticAt ℂ f ζ) (hu : AnalyticAt ℂ u ζ) (hune : u ζ ≠ 0)
    (hfac : δ =ᶠ[𝓝 ζ] fun z => (z - ζ) ^ 1 • u z) :
    DifferentiableAt ℂ
      (Function.update (fun z => f z / δ z - (f ζ / u ζ) / (z - ζ)) ζ
        (dslope (fun z => f z / u z) ζ ζ)) ζ := by
  set F : ℂ → ℂ := fun z => f z / u z with hF
  have hFan : AnalyticAt ℂ F ζ := hf.div hu hune
  -- On 𝓝[≠] ζ, the update equals dslope F ζ.
  have hune' : ∀ᶠ z in 𝓝 ζ, u z ≠ 0 := hu.continuousAt.eventually_ne hune
  have h₁ : (Function.update (fun z => f z / δ z - (f ζ / u ζ) / (z - ζ)) ζ (dslope F ζ ζ))
      =ᶠ[𝓝[≠] ζ] dslope F ζ := by
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
      hune'.filter_mono nhdsWithin_le_nhds] with z hzfac hzne hzune
    have hznez : z - ζ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hzne)
    rw [Function.update_of_ne (Set.mem_compl_singleton_iff.mp hzne)]
    simp only [hzfac, pow_one, smul_eq_mul]
    rw [dslope_of_ne F (Set.mem_compl_singleton_iff.mp hzne), slope_def_field, hF]
    field_simp
  have h₂ : (Function.update (fun z => f z / δ z - (f ζ / u ζ) / (z - ζ)) ζ (dslope F ζ ζ)) ζ
      = dslope F ζ ζ := Function.update_self ζ _ _
  have hev := eventuallyEq_nhds_of_eventuallyEq_nhdsNE h₁ h₂
  have hFdiff : ∀ᶠ z in 𝓝 ζ, DifferentiableAt ℂ F z :=
    hFan.eventually_analyticAt.mono (fun z h => h.differentiableAt)
  obtain ⟨s, hsub, hopen, hζs⟩ := eventually_nhds_iff.mp hFdiff
  have hsnhd : s ∈ 𝓝 ζ := hopen.mem_nhds hζs
  have hdsAt : DifferentiableAt ℂ (dslope F ζ) ζ :=
    ((differentiableOn_dslope hsnhd).mpr (fun z hz => (hsub z hz).differentiableWithinAt)).differentiableAt hsnhd
  exact hev.differentiableAt_iff.mpr hdsAt

end LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
