import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# The theta zero count (forward direction of the zero set)

This file proves the *forward* direction of the Jacobi theta zero set,

  `jacobiTheta₂ z Ω = 0  →  z ∈ (1+Ω)/2 + ℤ + Ω·ℤ`   (for `0 < Ω.im`),

complementing the reverse direction proved in `PrimitiveDerivativeSkeleton.lean`.  Mathlib
has **no** argument principle, but it **does** have Jensen's formula
(`MeromorphicOn.circleAverage_log_norm`) and the `divisor` counting machinery, so the route is:

1. θ is entire and not identically zero;
2. its `divisor` on a disk is the zero multiset (`MeromorphicOn`/`divisor`);
3. Jensen together with the order-2 growth of θ pins the exact count per cell to `1`;
4. combined with the reverse direction, this yields the forward inclusion.
-/

namespace LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount

open Complex MeromorphicOn
open scoped Topology

/-- **Verified.**  `θ(·, Ω) = jacobiTheta₂(·, Ω)` is entire for `Ω` in the upper
half-plane. -/
theorem theta_differentiable {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Differentiable ℂ (fun z => jacobiTheta₂ z Ω) :=
  fun z => differentiableAt_jacobiTheta₂_fst z hΩ

/-- **Verified.**  `θ(·, Ω)` is analytic on all of `ℂ`. -/
theorem theta_analyticOnNhd {Ω : ℂ} (hΩ : 0 < Ω.im) :
    AnalyticOnNhd ℂ (fun z => jacobiTheta₂ z Ω) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (theta_differentiable hΩ)

/-- **Verified.**  `θ(·, Ω)` is meromorphic on every set (it is entire). -/
theorem theta_meromorphicOn {Ω : ℂ} (hΩ : 0 < Ω.im) (U : Set ℂ) :
    MeromorphicOn (fun z => jacobiTheta₂ z Ω) U :=
  fun x _ => (theta_analyticOnNhd hΩ).meromorphicOn x (Set.mem_univ x)

/-- **Verified.**  The divisor of `θ` is nonnegative — it is entire, so it has only
zeros, no poles.  (This is what lets the Jensen divisor sum count *zeros*.) -/
theorem theta_divisor_nonneg {Ω : ℂ} (hΩ : 0 < Ω.im) (U : Set ℂ) :
    0 ≤ divisor (fun z => jacobiTheta₂ z Ω) U :=
  AnalyticOnNhd.divisor_nonneg (fun x _ => (theta_analyticOnNhd hΩ) x (Set.mem_univ x))

/-- **Verified.**  The zeros of `θ` in any ball form a finite set (so the Jensen
divisor sum is an honest finite count). -/
theorem theta_divisor_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) (R : ℝ) :
    (divisor (fun z => jacobiTheta₂ z Ω) (Metric.ball c R)).support.Finite :=
  divisor_ball_support_finite (theta_meromorphicOn hΩ (Metric.closedBall c R))

/-- **Verified — the zeros of `θ` in a *closed* ball are finite** (the divisor form used by
`theta_weighted_count_le`).  Derived from the open-ball finiteness via `closedBall 0 R ⊆ ball 0 (R+1)`
and domain-independence of the analytic order (`divisor_apply`). -/
theorem theta_divisor_closedBall_support_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (R : ℝ) :
    (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall 0 R)).support.Finite := by
  refine (theta_divisor_ball_finite hΩ 0 (R + 1)).subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  have huC : u ∈ Metric.closedBall (0 : ℂ) R := by
    by_contra h
    exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
  have huB : u ∈ Metric.ball (0 : ℂ) (R + 1) := by
    rw [Metric.mem_closedBall] at huC; rw [Metric.mem_ball]; linarith
  have hA : AnalyticOnNhd ℂ (fun z => jacobiTheta₂ z Ω) (Metric.closedBall 0 R) :=
    fun x _ => (theta_analyticOnNhd hΩ) x (Set.mem_univ x)
  have hA' : AnalyticOnNhd ℂ (fun z => jacobiTheta₂ z Ω) (Metric.ball 0 (R + 1)) :=
    fun x _ => (theta_analyticOnNhd hΩ) x (Set.mem_univ x)
  rw [hA.divisor_apply huC] at hu
  rw [hA'.divisor_apply huB]
  exact hu

/-! ## The zero count

The foundations above feed Jensen's formula `MeromorphicOn.circleAverage_log_norm`; the
lemmas below carry out the counting argument that pins the zero set down to one zero per
fundamental cell. -/

/-- **Verified — Fourier orthogonality.**  `∫₀¹ e^{2πi n x} dx = [n = 0]`.  This is the
self-contained heart of Residual A. -/
theorem integral_cexp_two_pi_I_mul (n : ℤ) :
    (∫ x in (0:ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)))
      = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) with hc_def
    have hc : c ≠ 0 := by
      rw [hc_def]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hn
    -- antiderivative F x = exp(c * x) / c
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c)
          (Complex.exp (c * (x : ℂ))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
      have h2 := h1.cexp
      have h3 := h2.div_const c
      simpa [mul_div_assoc, mul_comm, mul_div_cancel_left₀ _ hc] using h3
    have hint : ∫ x in (0:ℝ)..1, Complex.exp (c * (x : ℂ))
        = Complex.exp (c * (1 : ℂ)) / c - Complex.exp (c * (0 : ℂ)) / c := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      apply Continuous.intervalIntegrable
      exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have hexp1 : Complex.exp (c * (1 : ℂ)) = 1 := by
      rw [hc_def]
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (1 : ℂ)
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
      rw [Complex.exp_int_mul_two_pi_mul_I]
    rw [hint, hexp1]
    simp

/-- **Verified — per-term integral.**  `∫₀¹ θ_term(n, x, Ω) dx = e^{πi n² Ω} · [n=0]`. -/
theorem integral_jacobiTheta₂_term (Ω : ℂ) (n : ℤ) :
    (∫ x in (0:ℝ)..1, jacobiTheta₂_term n (x : ℂ) Ω)
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Ω) * (if n = 0 then 1 else 0) := by
  have hsplit : ∀ x : ℝ, jacobiTheta₂_term n (x : ℂ) Ω
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Ω) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
    intro x
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]
    ring_nf
  simp_rw [hsplit]
  rw [intervalIntegral.integral_const_mul, integral_cexp_two_pi_I_mul]

/-- **Verified — the period integral of `θ` is its `n=0` Fourier coefficient `= 1`.** -/
theorem theta_integral_eq_one {Ω : ℂ} (hΩ : 0 < Ω.im) :
    (∫ x in (0:ℝ)..1, jacobiTheta₂ (x : ℂ) Ω) = 1 := by
  set μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1) with hμ
  have hcont : ∀ n : ℤ, Continuous (fun x : ℝ => jacobiTheta₂_term n (x : ℂ) Ω) := by
    intro n; unfold jacobiTheta₂_term; fun_prop
  have hint : ∀ n : ℤ, MeasureTheory.Integrable (fun x : ℝ => jacobiTheta₂_term n (x : ℂ) Ω) μ :=
    fun n => (hcont n).integrableOn_Ioc
  have hnorm : ∀ n : ℤ,
      (∫ x, ‖jacobiTheta₂_term n (x : ℂ) Ω‖ ∂μ) = Real.exp (-Real.pi * (n : ℝ) ^ 2 * Ω.im) := by
    intro n
    have hpt : ∀ x : ℝ, ‖jacobiTheta₂_term n (x : ℂ) Ω‖ = Real.exp (-Real.pi * (n : ℝ) ^ 2 * Ω.im) := by
      intro x; rw [norm_jacobiTheta₂_term]; simp
    simp_rw [hpt, hμ, MeasureTheory.setIntegral_const]
    simp
  have hsum : Summable (fun n : ℤ => ∫ x, ‖jacobiTheta₂_term n (x : ℂ) Ω‖ ∂μ) := by
    have hs0 : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (0 : ℂ) Ω‖) :=
      summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff 0 Ω).mpr hΩ)
    refine hs0.congr (fun n => ?_)
    rw [hnorm n, norm_jacobiTheta₂_term]; simp
  have hterm : ∀ n : ℤ, (∫ x, jacobiTheta₂_term n (x : ℂ) Ω ∂μ)
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Ω) * (if n = 0 then 1 else 0) := by
    intro n
    rw [hμ, ← intervalIntegral.integral_of_le (zero_le_one)]
    exact integral_jacobiTheta₂_term Ω n
  calc (∫ x in (0:ℝ)..1, jacobiTheta₂ (x : ℂ) Ω)
      = ∫ x in (0:ℝ)..1, ∑' n : ℤ, jacobiTheta₂_term n (x : ℂ) Ω := by
        simp only [jacobiTheta₂]
    _ = ∫ x, (∑' n : ℤ, jacobiTheta₂_term n (x : ℂ) Ω) ∂μ := by
        rw [intervalIntegral.integral_of_le (zero_le_one), hμ]
    _ = ∑' n : ℤ, ∫ x, jacobiTheta₂_term n (x : ℂ) Ω ∂μ :=
        (MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = 1 := by
        simp_rw [hterm]
        rw [tsum_eq_single 0 (fun n hn => by rw [if_neg hn, mul_zero])]
        simp

/-- **Verified — `θ` is not identically zero.**  Its period integral is `1 ≠ 0`. -/
theorem theta_ne_zero_somewhere {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ∃ z : ℂ, jacobiTheta₂ z Ω ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hz : (∫ x in (0:ℝ)..1, jacobiTheta₂ (x : ℂ) Ω) = 0 := by
    have : (fun x : ℝ => jacobiTheta₂ (x : ℂ) Ω) = fun _ => 0 := by funext x; exact h _
    rw [this]; simp
  rw [theta_integral_eq_one hΩ] at hz
  exact one_ne_zero hz

/-- **Verified — first growth ingredient.**  `‖θ(z,Ω)‖` is bounded by the sum of its
term-norms (triangle inequality on the defining series).  The per-term norms are
`exp(-π(Ω.im·n² - 2|z.im|·|n|))` (`norm_jacobiTheta₂_term_le`), so this is the entry
point to the order-2 growth estimate that Jensen (Residual B) needs. -/
theorem norm_theta_le_tsum_norm {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    ‖jacobiTheta₂ z Ω‖ ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n z Ω‖ := by
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n z Ω‖) :=
    summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff z Ω).mpr hΩ)
  rw [jacobiTheta₂]
  exact norm_tsum_le_tsum_norm hs

/-- **Verified — exact gaussian form of the term norm.**  `‖θ_term(n,z,Ω)‖ =
exp(π·z.im²/Ω.im)·exp(−πΩ.im(n + z.im/Ω.im)²)`.  Signed completing-the-square on the
exact norm `exp(−πΩ.im·n² − 2π·n·z.im)`; cleaner than the `|n|` bound. -/
theorem norm_jacobiTheta₂_term_eq_gaussian {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) (n : ℤ) :
    ‖jacobiTheta₂_term n z Ω‖
      = Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
          Real.exp (-Real.pi * Ω.im * ((n : ℝ) + z.im / Ω.im) ^ 2) := by
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Verified — order-2 growth bound.**  `‖θ(z,Ω)‖ ≤ exp(π·z.im²/Ω.im) · G` where
`G = ∑ₙ exp(−πΩ.im(n + z.im/Ω.im)²)` is the (finite) shifted gaussian sum.  This is the
order-2 growth statement Jensen consumes; the only remaining growth step is a uniform
constant bound on `G` (its `1`-periodicity in the shift + compactness). -/
theorem norm_theta_growth_bound {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    ‖jacobiTheta₂ z Ω‖
      ≤ Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
          ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * ((n : ℝ) + z.im / Ω.im) ^ 2) := by
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n z Ω‖) :=
    summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff z Ω).mpr hΩ)
  calc ‖jacobiTheta₂ z Ω‖
      ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n z Ω‖ := norm_theta_le_tsum_norm hΩ z
    _ = ∑' n : ℤ, Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
            Real.exp (-Real.pi * Ω.im * ((n : ℝ) + z.im / Ω.im) ^ 2) := by
          exact tsum_congr (fun n => norm_jacobiTheta₂_term_eq_gaussian hΩ z n)
    _ = Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
          ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * ((n : ℝ) + z.im / Ω.im) ^ 2) :=
          tsum_mul_left

/-- **Verified — integer-shift periodicity of `G`** (generalizes the period-1 lemma).
Reduces any shift `b` to its fractional part in `[0,1)` for the uniform bound. -/
theorem shifted_gaussian_sum_int_periodic (T b : ℝ) (k : ℤ) :
    (∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + (b + (k : ℝ))) ^ 2))
      = ∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + b) ^ 2) := by
  have hcongr : ∀ n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + (b + (k : ℝ))) ^ 2)
      = Real.exp (-Real.pi * T * (((n + k : ℤ) : ℝ) + b) ^ 2) := by
    intro n; congr 2; push_cast; ring
  rw [tsum_congr hcongr]
  exact (Equiv.addRight k).tsum_eq
    (fun m : ℤ => Real.exp (-Real.pi * T * ((m : ℝ) + b) ^ 2))

/-- **Verified — gaussian summability.**  `∑ₙ exp(−πTn²)` is summable for `T > 0`
(the convergent constant bounding `G`).  Derived from `summable_jacobiTheta₂_term_iff`
at `z = 0`, `τ = iT`. -/
theorem summable_gaussian_int {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * T * (n : ℝ) ^ 2)) := by
  have him : 0 < (Complex.I * (T : ℂ)).im := by
    simp [Complex.mul_im, hT]
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 (Complex.I * (T : ℂ))‖) :=
    summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff 0 (Complex.I * (T : ℂ))).mpr him)
  refine hs.congr (fun n => ?_)
  rw [norm_jacobiTheta₂_term]
  simp [Complex.mul_im]
  ring_nf

/-- **Verified — uniform bound on the shifted gaussian sum `G`.**  `G(b) ≤ 2·∑ₙ exp(−πTn²)`
for every real shift `b`: reduce to the fractional part `r ∈ [0,1)` (periodicity), then
bound each term by `exp(−πTn²) + exp(−πT(n+1)²)`.  With `norm_theta_growth_bound` this is
the clean order-2 growth bound `‖θ(z)‖ ≤ C·exp(π·z.im²/Ω.im)`, `C = 2·∑ₙ exp(−πΩ.im·n²)`. -/
theorem shifted_gaussian_sum_le {T : ℝ} (hT : 0 < T) (b : ℝ) :
    (∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + b) ^ 2))
      ≤ 2 * ∑' n : ℤ, Real.exp (-Real.pi * T * (n : ℝ) ^ 2) := by
  have hsum0 : Summable (fun n : ℤ => Real.exp (-Real.pi * T * (n : ℝ) ^ 2)) :=
    summable_gaussian_int hT
  have hreindex : (∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2))
      = ∑' n : ℤ, Real.exp (-Real.pi * T * (n : ℝ) ^ 2) := by
    have hc : ∀ n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2)
        = Real.exp (-Real.pi * T * (((n + 1 : ℤ) : ℝ)) ^ 2) := by
      intro n; congr 2; push_cast; ring
    rw [tsum_congr hc]
    exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun m => Real.exp (-Real.pi * T * (m : ℝ) ^ 2))
  have hsum1 : Summable (fun n : ℤ => Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2)) := by
    have hc : (fun n : ℤ => Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2))
        = (fun m : ℤ => Real.exp (-Real.pi * T * (m : ℝ) ^ 2)) ∘ (fun n : ℤ => n + 1) := by
      funext n; simp only [Function.comp_apply]; congr 2; push_cast; ring
    rw [hc]; exact hsum0.comp_injective (add_left_injective 1)
  rw [show (∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + b) ^ 2))
      = ∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + Int.fract b) ^ 2) from by
        have h := shifted_gaussian_sum_int_periodic T (Int.fract b) ⌊b⌋
        rwa [show Int.fract b + (⌊b⌋ : ℝ) = b from by rw [Int.fract]; ring] at h]
  set r := Int.fract b with hr
  have hr0 : 0 ≤ r := Int.fract_nonneg b
  have hr1 : r < 1 := Int.fract_lt_one b
  have hbound : ∀ n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + r) ^ 2)
      ≤ Real.exp (-Real.pi * T * (n : ℝ) ^ 2) + Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2) := by
    intro n
    rcases le_or_gt 0 n with hn | hn
    · have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsq : (n : ℝ) ^ 2 ≤ ((n : ℝ) + r) ^ 2 := by nlinarith [mul_nonneg hn' hr0]
      have hle : Real.exp (-Real.pi * T * ((n : ℝ) + r) ^ 2)
          ≤ Real.exp (-Real.pi * T * (n : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_pos Real.pi_pos hT).le (sub_nonneg.mpr hsq)]
      linarith [Real.exp_nonneg (-Real.pi * T * ((n : ℝ) + 1) ^ 2)]
    · have hn1 : (n : ℝ) + 1 ≤ 0 := by
        have hni : n ≤ -1 := by omega
        have h2 : (n : ℝ) ≤ -1 := by exact_mod_cast hni
        linarith
      have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + r) ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - r from by linarith)
          (show (0 : ℝ) ≤ -(2 * (n : ℝ) + r + 1) from by linarith), hr0, hr1, hn1]
      have hle : Real.exp (-Real.pi * T * ((n : ℝ) + r) ^ 2)
          ≤ Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_pos Real.pi_pos hT).le (sub_nonneg.mpr hsq)]
      linarith [Real.exp_nonneg (-Real.pi * T * (n : ℝ) ^ 2)]
  have hsumr : Summable (fun n : ℤ => Real.exp (-Real.pi * T * ((n : ℝ) + r) ^ 2)) :=
    Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) hbound (hsum0.add hsum1)
  calc (∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + r) ^ 2))
      ≤ ∑' n : ℤ, (Real.exp (-Real.pi * T * (n : ℝ) ^ 2)
          + Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2)) :=
        hsumr.tsum_le_tsum hbound (hsum0.add hsum1)
    _ = (∑' n : ℤ, Real.exp (-Real.pi * T * (n : ℝ) ^ 2))
          + ∑' n : ℤ, Real.exp (-Real.pi * T * ((n : ℝ) + 1) ^ 2) := hsum0.tsum_add hsum1
    _ = 2 * ∑' n : ℤ, Real.exp (-Real.pi * T * (n : ℝ) ^ 2) := by rw [hreindex]; ring

/-- **Verified — complete order-2 growth bound (capstone).**  `‖θ(z,Ω)‖ ≤ C·exp(π·z.im²/Ω.im)`
with the explicit `Ω`-only constant `C = 2·∑ₙ exp(−πΩ.im·n²)`.  Combines `norm_theta_growth_bound`
with the uniform `G`-bound.  This is the growth input Jensen's formula needs (Residual B); the
remaining work is the asymptotic circle-average count, not the growth. -/
theorem norm_theta_le_const_mul_exp {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    ‖jacobiTheta₂ z Ω‖
      ≤ (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2)) *
          Real.exp (Real.pi * z.im ^ 2 / Ω.im) := by
  calc ‖jacobiTheta₂ z Ω‖
      ≤ Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
          ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * ((n : ℝ) + z.im / Ω.im) ^ 2) :=
        norm_theta_growth_bound hΩ z
    _ ≤ Real.exp (Real.pi * z.im ^ 2 / Ω.im) *
          (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (shifted_gaussian_sum_le hΩ (z.im / Ω.im)) (Real.exp_nonneg _)
    _ = (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2)) *
          Real.exp (Real.pi * z.im ^ 2 / Ω.im) := by ring

/-- **Verified — upper-side Jensen asymptotic.**  `circleAverage(log‖θ‖) 0 R ≤ log C + π·R²/(2Ω.im)`
with `C = 2·∑ₙ exp(−πΩ.im·n²)`.  From the order-2 growth bound (pointwise `log`, with `C ≥ 2`
making the bound hold even at zeros where `log 0 = 0`), circle-average monotonicity, and
`circleAverage_im_sq`.  This is the leading `R²` term Jensen turns into the zero count;
the matching lower estimate is the remaining (multi-session) piece of Residual B. -/
theorem circleAverage_log_norm_theta_le {Ω : ℂ} (hΩ : 0 < Ω.im) {R : ℝ} (hR : 0 ≤ R) :
    Real.circleAverage (fun z => Real.log ‖jacobiTheta₂ z Ω‖) 0 R
      ≤ Real.log (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2))
        + Real.pi / Ω.im * (R ^ 2 / 2) := by
  set C := 2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2) with hC
  have hge1 : (1 : ℝ) ≤ ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2) := by
    have h0 := sum_le_hasSum {(0 : ℤ)} (fun i _ => Real.exp_nonneg _)
      (summable_gaussian_int hΩ).hasSum
    simpa using h0
  have hCpos : 0 < C := by rw [hC]; linarith
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hpt : ∀ z : ℂ, Real.log ‖jacobiTheta₂ z Ω‖ ≤ Real.log C + Real.pi * z.im ^ 2 / Ω.im := by
    intro z
    rcases (norm_nonneg (jacobiTheta₂ z Ω)).lt_or_eq with h0 | h0
    · have hb := norm_theta_le_const_mul_exp hΩ z
      calc Real.log ‖jacobiTheta₂ z Ω‖
          ≤ Real.log (C * Real.exp (Real.pi * z.im ^ 2 / Ω.im)) := Real.log_le_log h0 hb
        _ = Real.log C + Real.pi * z.im ^ 2 / Ω.im := by
            rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    · rw [← h0, Real.log_zero]
      have h1 : 0 ≤ Real.log C := Real.log_nonneg hC1
      have h2 : 0 ≤ Real.pi * z.im ^ 2 / Ω.im := by positivity
      linarith
  have hint1 : CircleIntegrable (fun z => Real.log ‖jacobiTheta₂ z Ω‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm (theta_meromorphicOn hΩ (Metric.sphere 0 |R|))
  have hint2 : CircleIntegrable (fun z : ℂ => Real.log C + Real.pi * z.im ^ 2 / Ω.im) 0 R := by
    apply ContinuousOn.circleIntegrable hR
    apply Continuous.continuousOn
    fun_prop
  calc Real.circleAverage (fun z => Real.log ‖jacobiTheta₂ z Ω‖) 0 R
      ≤ Real.circleAverage (fun z : ℂ => Real.log C + Real.pi * z.im ^ 2 / Ω.im) 0 R :=
        Real.circleAverage_mono hint1 hint2 (fun x _ => hpt x)
    _ = Real.log C + Real.pi / Ω.im * (R ^ 2 / 2) := by
        rw [Real.circleAverage_def]
        have hfun : ∀ θ : ℝ,
            Real.log C + Real.pi * (circleMap 0 R θ).im ^ 2 / Ω.im
              = Real.log C + (Real.pi * R ^ 2 / Ω.im) * Real.sin θ ^ 2 := by
          intro θ
          have him : (circleMap 0 R θ).im = R * Real.sin θ := by
            simp [circleMap, Complex.mul_im, Complex.exp_ofReal_mul_I_im,
              Complex.exp_ofReal_mul_I_re]
          rw [him]; ring
        simp_rw [hfun]
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (by apply Continuous.intervalIntegrable; fun_prop),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_sin_sq]
        simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi, smul_eq_mul,
          sub_zero]
        field_simp
        ring

/-- **Verified — Jensen's formula for θ.**  The instantiation of
`MeromorphicOn.circleAverage_log_norm` at `f = θ(·,Ω)`, `c = 0`.  The left side is the
circle-average we bounded above; the right side is the weighted zero count (`θ` is entire,
so the divisor counts only zeros).  Equating the two is the bridge from the growth
asymptotic to the count. -/
theorem theta_jensen {Ω : ℂ} (hΩ : 0 < Ω.im) {R : ℝ} (hR : R ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖jacobiTheta₂ z Ω‖) 0 R
      = (∑ᶠ u, (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) u
            * Real.log (R * ‖(0 : ℂ) - u‖⁻¹))
        + (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) 0 * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (fun z => jacobiTheta₂ z Ω) 0‖ :=
  MeromorphicOn.circleAverage_log_norm hR (theta_meromorphicOn hΩ (Metric.closedBall (0 : ℂ) |R|))

/-- **Verified — upper bound on the weighted zero count.**  Jensen's formula for θ
combined with the upper-side asymptotic: the weighted divisor sum is `≤ log C + π·R²/(2Ω.im)`.
This is the upper half of the count.  (The matching *lower* bound — which forces the
count to equal the lattice density rather than merely not exceed this — is the remaining
multi-session piece.) -/
theorem theta_weighted_count_le {Ω : ℂ} (hΩ : 0 < Ω.im) {R : ℝ} (hR : 0 < R) :
    (∑ᶠ u, (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) u
          * Real.log (R * ‖(0 : ℂ) - u‖⁻¹))
        + (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) 0 * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (fun z => jacobiTheta₂ z Ω) 0‖
      ≤ Real.log (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2))
        + Real.pi / Ω.im * (R ^ 2 / 2) := by
  rw [← theta_jensen hΩ hR.ne']
  exact circleAverage_log_norm_theta_le hΩ hR.le

/-- **Verified — `θ`'s analytic order is finite everywhere.**  If it were `⊤` at some `u`,
`θ` would vanish on a neighbourhood, hence (identity theorem on connected `ℂ`) be identically
zero — contradicting `theta_ne_zero_somewhere`. -/
theorem theta_analyticOrderAt_ne_top {Ω : ℂ} (hΩ : 0 < Ω.im) (u : ℂ) :
    analyticOrderAt (fun z => jacobiTheta₂ z Ω) u ≠ ⊤ := by
  rw [Ne, analyticOrderAt_eq_top]
  intro hev
  obtain ⟨z₀, hz₀⟩ := theta_ne_zero_somewhere hΩ
  exact hz₀ ((theta_analyticOnNhd hΩ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ u) hev (Set.mem_univ z₀))

/-- **Verified — `divisor ≥ 1` at a zero of `θ`.**  Each zero contributes at least `1` to the
divisor.  This is the lower-bound ingredient: applied at the (proved) lattice zeros it gives
`Σ divisor·log(R/|u|) ≥ Σ_{lattice} log(R/|u|)`. -/
theorem theta_divisor_ge_one_of_zero {Ω : ℂ} (hΩ : 0 < Ω.im) {U : Set ℂ} {u : ℂ} (hu : u ∈ U)
    (hz : jacobiTheta₂ u Ω = 0) : 1 ≤ divisor (fun z => jacobiTheta₂ z Ω) U u := by
  have hA : AnalyticOnNhd ℂ (fun z => jacobiTheta₂ z Ω) U :=
    fun x _ => (theta_analyticOnNhd hΩ) x (Set.mem_univ x)
  rw [hA.divisor_apply hu]
  have hAt : AnalyticAt ℂ (fun z => jacobiTheta₂ z Ω) u :=
    (theta_analyticOnNhd hΩ) u (Set.mem_univ u)
  have hne0 : analyticOrderAt (fun z => jacobiTheta₂ z Ω) u ≠ 0 :=
    hAt.analyticOrderAt_ne_zero.mpr hz
  have hnetop := theta_analyticOrderAt_ne_top hΩ u
  set o := analyticOrderAt (fun z => jacobiTheta₂ z Ω) u with ho
  lift o to ℕ using hnetop with m
  rw [ENat.map_coe, WithTop.untop₀_coe]
  have hm0 : m ≠ 0 := by rintro rfl; exact hne0 rfl
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0

/-- **Verified — half-period zero** (self-contained for `jacobiTheta₂`).  `θ((1+Ω)/2, Ω) = 0`,
from evenness + the two quasi-periodicity laws; no counting.  This is the base point whose
lattice translates are the zeros that supply the lower bound. -/
theorem jacobiTheta₂_half_period_eq_zero (Ω : ℂ) :
    jacobiTheta₂ ((1 + Ω) / 2) Ω = 0 := by
  have key : jacobiTheta₂ ((1 + Ω) / 2) Ω = - jacobiTheta₂ ((1 + Ω) / 2) Ω := by
    calc jacobiTheta₂ ((1 + Ω) / 2) Ω
        = jacobiTheta₂ ((-((1 + Ω) / 2) + Ω) + 1) Ω := by congr 1; ring
      _ = jacobiTheta₂ (-((1 + Ω) / 2) + Ω) Ω := jacobiTheta₂_add_left _ Ω
      _ = Complex.exp (-↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2))))
            * jacobiTheta₂ (-((1 + Ω) / 2)) Ω := jacobiTheta₂_add_left' _ Ω
      _ = Complex.exp (-↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2))))
            * jacobiTheta₂ ((1 + Ω) / 2) Ω := by rw [jacobiTheta₂_neg_left]
      _ = (-1 : ℂ) * jacobiTheta₂ ((1 + Ω) / 2) Ω := by
            congr 1
            rw [show -↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2)))
                = (↑Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
      _ = - jacobiTheta₂ ((1 + Ω) / 2) Ω := by ring
  linear_combination (1 / 2 : ℂ) * key

/-- **Order factorization at the half-period.**  Near its zero `ζ = (1+Ω)/2`, the theta factors as
`θ = (z−ζ)^m • u` with `u` analytic and `u ζ ≠ 0` and order `m ≥ 1` (finite by the identity theorem,
`≥ 1` since `θ ζ = 0`).  This is the input to the log-derivative principal part (`θ'/θ` has a simple
pole with residue `m` at `ζ`), which the argument-principle simple-zero computation consumes. -/
theorem theta_order_factorization {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ∃ (m : ℕ) (u : ℂ → ℂ), 1 ≤ m ∧ AnalyticAt ℂ u ((1 + Ω) / 2) ∧ u ((1 + Ω) / 2) ≠ 0 ∧
      (fun z => jacobiTheta₂ z Ω) =ᶠ[𝓝 ((1 + Ω) / 2)]
        fun z => (z - (1 + Ω) / 2) ^ m • u z := by
  set ζ := (1 + Ω) / 2 with hζ
  have hAt : AnalyticAt ℂ (fun z => jacobiTheta₂ z Ω) ζ :=
    (theta_analyticOnNhd hΩ) ζ (Set.mem_univ ζ)
  have hz : jacobiTheta₂ ζ Ω = 0 := jacobiTheta₂_half_period_eq_zero Ω
  have hne0 : analyticOrderAt (fun z => jacobiTheta₂ z Ω) ζ ≠ 0 :=
    hAt.analyticOrderAt_ne_zero.mpr hz
  have hnetop := theta_analyticOrderAt_ne_top hΩ ζ
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hordm : analyticOrderAt (fun z => jacobiTheta₂ z Ω) ζ = (m : ℕ∞) := hm.symm
  obtain ⟨u, hu, hune, hfac⟩ := hAt.analyticOrderAt_eq_natCast.mp hordm
  refine ⟨m, u, ?_, hu, hune, hfac⟩
  rw [hordm] at hne0
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)

/-- `logDeriv θ = θ'/θ` — bridges `logDeriv` (used by the argument-principle machinery) to the
`jacobiTheta₂'/jacobiTheta₂` form of the skeleton's log-derivative quasi-periodicity laws
(`jacobiTheta₂_logDeriv_add_one`, `..._add_tau`), via `hasDerivAt_jacobiTheta₂_fst`. -/
theorem logDeriv_jacobiTheta₂_eq {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    logDeriv (fun z => jacobiTheta₂ z Ω) z = jacobiTheta₂' z Ω / jacobiTheta₂ z Ω := by
  rw [logDeriv_apply, (hasDerivAt_jacobiTheta₂_fst z hΩ).deriv]

/-- ℝ-independence of `1` and `Ω` (`Ω ∉ ℝ`): `s + tΩ = s' + t'Ω ⟹ s = s' ∧ t = t'`. -/
theorem coord_indep_real {Ω : ℂ} (hΩ : Ω.im ≠ 0) (s t s' t' : ℝ)
    (h : (s : ℂ) + (t : ℂ) * Ω = (s' : ℂ) + (t' : ℂ) * Ω) : s = s' ∧ t = t' := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    zero_mul, mul_zero, add_zero, zero_add] at him
  have ht : t = t' := mul_right_cancel₀ hΩ him
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  rw [ht] at hre; exact ⟨by linarith, ht⟩

/-- **Verified — integer-translation invariance** (period `1`, extended to `ℤ`). -/
theorem jacobiTheta₂_add_intCast (Ω z : ℂ) (m : ℤ) :
    jacobiTheta₂ (z + (m : ℂ)) Ω = jacobiTheta₂ z Ω := by
  have hper : Function.Periodic (fun w => jacobiTheta₂ w Ω) 1 := fun w => jacobiTheta₂_add_left w Ω
  simpa using hper.sub_int_mul_eq (x := z) (-m)

/-- **Verified — zeros persist under integer `Ω`-translation.** -/
theorem jacobiTheta₂_eq_zero_add_intCast_mul_tau (Ω z : ℂ) (n : ℤ)
    (h : jacobiTheta₂ z Ω = 0) : jacobiTheta₂ (z + (n : ℂ) * Ω) Ω = 0 := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ k ih =>
      have e : z + (((k : ℤ) + 1 : ℤ) : ℂ) * Ω = (z + ((k : ℤ) : ℂ) * Ω) + Ω := by push_cast; ring
      rw [e, jacobiTheta₂_add_left', ih, mul_zero]
  | pred k ih =>
      push_cast at ih ⊢
      rw [show z + (-(k : ℂ) - 1) * Ω = (z + -(k : ℂ) * Ω) - Ω from by ring]
      have h0 := jacobiTheta₂_add_left' ((z + -(k : ℂ) * Ω) - Ω) Ω
      rw [show ((z + -(k : ℂ) * Ω) - Ω) + Ω = z + -(k : ℂ) * Ω from by ring, ih] at h0
      exact (mul_eq_zero.mp h0.symm).resolve_left (Complex.exp_ne_zero _)

/-- **Verified — zeros are lattice-translation invariant.**  If `θ(z) = 0` then `θ(z + m + nΩ) = 0`
for all integers `m, n` — so the zero set is a union of cosets of `ℤ + Ωℤ`.  This makes the *second*
coset `z + L` in the matching argument (d) consist entirely of zeros. -/
theorem jacobiTheta₂_eq_zero_translate {Ω z : ℂ} (h : jacobiTheta₂ z Ω = 0) (m n : ℤ) :
    jacobiTheta₂ (z + (m : ℂ) + (n : ℂ) * Ω) Ω = 0 := by
  rw [show z + (m : ℂ) + (n : ℂ) * Ω = (z + (n : ℂ) * Ω) + (m : ℂ) from by ring,
    jacobiTheta₂_add_intCast]
  exact jacobiTheta₂_eq_zero_add_intCast_mul_tau Ω z n h

/-- **Verified — the full lattice zeros.**  `θ` vanishes at every `(1+Ω)/2 + m + nΩ`. -/
theorem jacobiTheta₂_eq_zero_at_lattice (Ω : ℂ) (m n : ℤ) :
    jacobiTheta₂ ((1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) Ω = 0 := by
  rw [show (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω = ((1 + Ω) / 2 + (n : ℂ) * Ω) + (m : ℂ) from by ring,
    jacobiTheta₂_add_intCast]
  exact jacobiTheta₂_eq_zero_add_intCast_mul_tau Ω ((1 + Ω) / 2) n (jacobiTheta₂_half_period_eq_zero Ω)

/-- **Verified — `divisor ≥ 1` at every lattice point.**  Completes the per-point lower
bound: combined with the (multi-session) lattice-sum asymptotic this squeezes the count. -/
theorem theta_divisor_ge_one_at_lattice {Ω : ℂ} (hΩ : 0 < Ω.im) {U : Set ℂ} (m n : ℤ)
    (hu : (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω ∈ U) :
    1 ≤ divisor (fun z => jacobiTheta₂ z Ω) U ((1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) :=
  theta_divisor_ge_one_of_zero hΩ hu (jacobiTheta₂_eq_zero_at_lattice Ω m n)

/-- **Verified — finitely many lattice points in a disk.**  Derived cleanly: lattice points
are zeros (proved), so they sit in the divisor support, which is finite on any ball.  This is
the finiteness the lattice-point count is taken over. -/
theorem lattice_in_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (R : ℝ) :
    {z : ℂ | (∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧
      z ∈ Metric.ball (0 : ℂ) R}.Finite := by
  refine (theta_divisor_ball_finite hΩ 0 R).subset ?_
  rintro z ⟨⟨m, n, rfl⟩, hzin⟩
  have h1 := theta_divisor_ge_one_at_lattice hΩ m n hzin
  simp only [Function.mem_support, ne_eq]
  intro hzero
  rw [hzero] at h1
  exact absurd h1 (by norm_num)

/-- **Verified — lattice basis is `ℝ`-linearly independent.**  `{1, Ω}` is `ℝ`-independent
for `Im Ω > 0`, so `ℤ + Ωℤ = span ℤ {1, Ω}` is a genuine `ZLattice` (Mathlib `PeriodPair`).
This is the structural foundation for the covolume (`= Im Ω`) and the lattice count. -/
theorem lattice_linearIndependent {Ω : ℂ} (hΩ : 0 < Ω.im) :
    LinearIndependent ℝ ![(1 : ℂ), Ω] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_one, zero_mul, add_zero, zero_add, Complex.zero_im] at him
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 (ne_of_gt hΩ)
  subst ht
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_one, zero_mul, sub_zero, add_zero, Complex.zero_re] at hre
  exact ⟨hre, rfl⟩

/-- **Verified — the half-period is not a lattice point.**  `(1+Ω)/2 ∉ ℤ + Ωℤ` (imaginary
parts force `n = 1/2`).  So the zero coset `(1+Ω)/2 + ℤ + Ωℤ` is disjoint from the lattice
— consistent with `θ(0) ≠ 0`. -/
theorem half_period_not_lattice {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ¬ ∃ m n : ℤ, (1 + Ω) / 2 = (m : ℂ) + (n : ℂ) * Ω := by
  rintro ⟨m, n, h⟩
  have h2 : (1 + Ω) = 2 * ((m : ℂ) + (n : ℂ) * Ω) := by rw [← h]; ring
  have him := congrArg Complex.im h2
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.intCast_im,
    Complex.intCast_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_add, add_zero, zero_mul] at him
  have hn : (2 : ℝ) * (n : ℝ) = 1 := by
    have hne : Ω.im ≠ 0 := ne_of_gt hΩ
    field_simp at him
    nlinarith [him, hΩ]
  have : (2 : ℤ) * n = 1 := by exact_mod_cast hn
  omega

/-- **Verified — `{1, Ω}` is `ℤ`-linearly independent.**  Restricting scalars from the `ℝ`-independence;
gives the lattice's `ℤ`-basis (`Basis.span`), the input to the covolume determinant. -/
theorem lattice_linearIndependent_int {Ω : ℂ} (hΩ : 0 < Ω.im) :
    LinearIndependent ℤ ![(1 : ℂ), Ω] := by
  apply (lattice_linearIndependent hΩ).restrict_scalars
  intro a b hab
  simpa using hab

/-- **Verified — the basis determinant `= Im Ω`.**  `det_{1,I}(1, Ω) = Im Ω`.  This is the
`|det|` factor in `covolume_eq_det_mul_measureReal`, giving covolume `= Im Ω · vol(unit cell)`. -/
theorem basisOneI_det_one_Omega (Ω : ℂ) :
    Complex.basisOneI.det ![1, Ω] = Ω.im := by
  rw [Complex.basisOneI.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.coe_basisOneI_repr, Complex.one_re, Complex.one_im]
  ring

/-- **Verified — the unit cell has volume `1`.**  `basisOneI` is orthonormal, so its addHaar
measure is `volume` and the parallelepiped (≈ fundamental domain a.e.) has measure `1`. -/
theorem parallelepiped_basisOneI_volume :
    MeasureTheory.volume (_root_.parallelepiped ⇑Complex.basisOneI) = 1 := by
  have hcoe : ⇑Complex.basisOneI = ⇑Complex.orthonormalBasisOneI := by
    rw [Complex.coe_basisOneI, Complex.coe_orthonormalBasisOneI]
  rw [hcoe]
  exact Complex.orthonormalBasisOneI.volume_parallelepiped

/-- **Verified — the covolume is `Im Ω`.**  `covolume(ℤ + Ωℤ) = Im Ω` (for `Im Ω > 0`):
assembles the determinant piece (`= Im Ω`) and the unit-cell volume (`= 1`) through
`ZLattice.covolume_eq_det_mul_measureReal`.  This is the constant in the lattice-sum asymptotic. -/
theorem lattice_covolume {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ZLattice.covolume (Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])) MeasureTheory.volume = Ω.im := by
  classical
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    rw [Fintype.card_fin, Complex.finrank_real_complex]
  set bR : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank (lattice_linearIndependent hΩ) hcard with hbR_def
  have hbR : ⇑bR = ![(1 : ℂ), Ω] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rw [show Submodule.span ℤ (Set.range ![(1 : ℂ), Ω]) = Submodule.span ℤ (Set.range ⇑bR) from by
    rw [hbR]]
  have hliZ : LinearIndependent ℤ ⇑bR := by rw [hbR]; exact lattice_linearIndependent_int hΩ
  rw [ZLattice.covolume_eq_det_mul_measureReal (μ := MeasureTheory.volume)
    (b := Module.Basis.span hliZ) (b₀ := Complex.basisOneI)]
  have hcomp : ((↑) ∘ ⇑(Module.Basis.span hliZ)) = ![(1 : ℂ), Ω] := by
    funext i
    simp only [Function.comp_apply, Module.Basis.span_apply, hbR]
  rw [hcomp, basisOneI_det_one_Omega, abs_of_pos hΩ,
    MeasureTheory.measureReal_congr
      (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI MeasureTheory.volume),
    MeasureTheory.measureReal_def, parallelepiped_basisOneI_volume]
  simp

/-- **Verified — Gauss-circle leading count for the period lattice.**  Instantiating Mathlib's
`ZLattice.covolume.tendsto_card_le_div'` with the degree-2 homogeneous norm-square `F = ‖·‖²`
(so `{F ≤ c}` is the disk of radius `√c`): the lattice-point count divided by `c` tends to
`vol(unit disk)/covolume = π / Im Ω`.  This is the leading term `N(R) ~ (π/Im Ω)·R²` that the
log-weighted lattice-sum asymptotic integrates against. -/
theorem theta_lattice_disk_count {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto
      (fun c : ℝ => (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ c} ∩
        (Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])) : Set ℂ) : ℝ) / c)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  classical
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    rw [Fintype.card_fin, Complex.finrank_real_complex]
  set bR : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank (lattice_linearIndependent hΩ) hcard with hbR_def
  have hbR : ⇑bR = ![(1 : ℂ), Ω] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hspan : Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])
      = Submodule.span ℤ (Set.range ⇑bR) := by rw [hbR]
  have hset : {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h; nlinarith [norm_nonneg x]
    · intro h; nlinarith [norm_nonneg x]
  have hcovbR : ZLattice.covolume (Submodule.span ℤ (Set.range ⇑bR)) MeasureTheory.volume = Ω.im := by
    rw [← hspan]; exact lattice_covolume hΩ
  have hvol : MeasureTheory.volume.real {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ 1}
      = Real.pi := by
    rw [hset, MeasureTheory.measureReal_def, Complex.volume_closedBall]
    simp [NNReal.coe_real_pi]
  have key := ZLattice.covolume.tendsto_card_le_div'
    (L := Submodule.span ℤ (Set.range ⇑bR))
    (X := (Set.univ : Set ℂ)) (F := fun x : ℂ => ‖x‖ ^ 2)
    (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by
      rw [Complex.finrank_real_complex, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]; ring)
    (by show Bornology.IsBounded {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ 1}
        rw [hset]; exact Metric.isBounded_closedBall)
    (by show MeasurableSet {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ 1}
        rw [hset]; exact measurableSet_closedBall)
    (by show MeasureTheory.volume (frontier {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ 1}) = 0
        rw [hset, frontier_closedBall' (0 : ℂ) 1]
        exact MeasureTheory.Measure.addHaar_sphere _ _ _)
  rw [hvol, hcovbR, ← hspan] at key
  exact key

/-- **Verified — Gauss-circle count by radius.**  The radius-parametrized form of
`theta_lattice_disk_count` (substitute `c = R²`): the lattice-point count in the closed disk of
radius `R` divided by `R²` tends to `π / Im Ω`.  This is the count-by-radius `N(R)/R² → π/Im Ω`
that the log-weighted Abel/Tonelli step integrates. -/
theorem theta_lattice_disk_count_radius {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto
      (fun R : ℝ => (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        (Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])) : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) :=
  (theta_lattice_disk_count hΩ).comp (Filter.tendsto_pow_atTop two_ne_zero)

/-- **Verified — lattice span membership as integer combinations.**  `z ∈ span ℤ {1, Ω}` iff
`z = m + nΩ` for integers `m, n`.  Bridges the two lattice representations used here: the
`Submodule.span` form (in the covolume/count lemmas) and the explicit `∃ m n` form (in the
divisor/zero lemmas and the half-period coset). -/
theorem mem_lattice_span_iff {Ω z : ℂ} :
    z ∈ Submodule.span ℤ (Set.range ![(1 : ℂ), Ω]) ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * Ω := by
  rw [show Set.range ![(1 : ℂ), Ω] = {(1 : ℂ), Ω} from by
    ext w; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]]
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← h]; ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

/-- **Verified — lattice points in a disk are finite.**  The set of lattice points `l ∈ span ℤ {1,Ω}`
with `‖l‖² ≤ c` is finite (a `ZLattice` meets any bounded set in finitely many points).  Supplies the
`Nat.card` monotonicity used in the coset-count squeeze. -/
theorem lattice_span_in_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℝ) :
    ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ c} ∩
      (Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])) : Set ℂ).Finite := by
  classical
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    rw [Fintype.card_fin, Complex.finrank_real_complex]
  set bR : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank (lattice_linearIndependent hΩ) hcard with hbRdef
  have hbR : ⇑bR = ![(1 : ℂ), Ω] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hspan : Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])
      = Submodule.span ℤ (Set.range ⇑bR) := by rw [hbR]
  rw [hspan]
  have hbdd : Bornology.IsBounded {x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ c} := by
    apply Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.sqrt (max c 0)))
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and] at hx
    rw [Metric.mem_closedBall, dist_zero_right, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt (le_trans hx (le_max_left _ _))
  exact ZSpan.setFinite_inter (b := bR) hbdd

/-- **Verified — reparametrized lattice count.**  Shifting the disk radius by a constant `k` does
not change the leading count: `#(L ∩ {‖x‖² ≤ (R+k)²})/R² → π/Im Ω`.  (`(R+k)²/R² = (1+k/R)² → 1`.)
The two shifted counts `k = ±‖v‖` sandwich the half-period coset count. -/
theorem count_reparam_shift {Ω : ℂ} (hΩ : 0 < Ω.im) (k : ℝ) :
    Filter.Tendsto (fun R : ℝ =>
      (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + k) ^ 2} ∩
        (Submodule.span ℤ (Set.range ![(1 : ℂ), Ω])) : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  have hFshift := (theta_lattice_disk_count_radius hΩ).comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop k Filter.tendsto_id)
  have hratio : Filter.Tendsto (fun R : ℝ => (R + k) ^ 2 / R ^ 2) Filter.atTop (nhds 1) := by
    have hkR : Filter.Tendsto (fun R : ℝ => k / R) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h1 : Filter.Tendsto (fun R : ℝ => (1 + k / R) ^ 2) Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun R : ℝ => 1 + k / R) Filter.atTop (nhds 1) := by
        simpa using hkR.const_add 1
      simpa using h0.pow 2
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    field_simp
  have hmul := hFshift.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 0 (-k))] with R hR
  have hR0 : 0 < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRk : R + k ≠ 0 := by
    have : -k < R := lt_of_le_of_lt (le_max_right _ _) hR
    linarith
  simp only [Function.comp_apply, id_eq]
  field_simp [hRk, hR0.ne']

/-- **Verified — Gauss-circle count for the half-period coset.**  The count of coset points
`(1+Ω)/2 + ℤ + Ωℤ` in the disk of radius `R`, over `R²`, tends to `π/Im Ω` — the same leading
density as the lattice (translation-invariant leading term), by sandwiching between the two shifted
lattice counts `count_reparam_shift (±‖v‖)` via the triangle inequality.  Part (a′) of the valence
count: the half-period coset alone carries the full Jensen budget. -/
theorem theta_coset_disk_count {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun R : ℝ =>
      (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  set v : ℂ := (1 + Ω) / 2 with hvdef
  set L := Submodule.span ℤ (Set.range ![(1 : ℂ), Ω]) with hLdef
  -- coset count = count of lattice points `l` with `‖v + l‖² ≤ R²`
  have hbij : ∀ R : ℝ,
      Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = v + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ)
      = Nat.card {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖v + l‖ ^ 2 ≤ R ^ 2} := by
    intro R
    have hset : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = v + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ)
        = (fun l => v + l) '' {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖v + l‖ ^ 2 ≤ R ^ 2} := by
      ext x
      constructor
      · rintro ⟨⟨_, hnorm⟩, m, n, rfl⟩
        refine ⟨(m : ℂ) + (n : ℂ) * Ω, ⟨mem_lattice_span_iff.mpr ⟨m, n, rfl⟩, ?_⟩, by ring⟩
        rw [show v + ((m : ℂ) + (n : ℂ) * Ω) = v + (m : ℂ) + (n : ℂ) * Ω from by ring]
        exact hnorm
      · rintro ⟨l, ⟨hlL, hlnorm⟩, rfl⟩
        obtain ⟨m, n, rfl⟩ := mem_lattice_span_iff.mp hlL
        exact ⟨⟨trivial, hlnorm⟩, m, n, by ring⟩
    rw [hset, Nat.card_image_of_injective (add_right_injective v)]
  -- coset lattice-set is finite (contained in a lattice disk)
  have hcosetfin : ∀ R : ℝ, {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖v + l‖ ^ 2 ≤ R ^ 2}.Finite := by
    intro R
    refine (lattice_span_in_ball_finite hΩ ((|R| + ‖v‖) ^ 2)).subset ?_
    rintro l ⟨hlL, hln⟩
    refine ⟨⟨trivial, ?_⟩, hlL⟩
    have h1 : ‖v + l‖ ≤ |R| := by
      rw [← Real.sqrt_sq (abs_nonneg R), ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (le_trans hln (by rw [sq_abs]))
    have h2 : ‖l‖ ≤ |R| + ‖v‖ := by
      calc ‖l‖ = ‖v + l - v‖ := by ring_nf
        _ ≤ ‖v + l‖ + ‖v‖ := norm_sub_le _ _
        _ ≤ |R| + ‖v‖ := by linarith
    nlinarith [norm_nonneg l, norm_nonneg v, abs_nonneg R]
  simp only [hbij]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (count_reparam_shift hΩ (-‖v‖)) (count_reparam_shift hΩ ‖v‖) ?_ ?_
  · -- lower: count at radius `R - ‖v‖`  ≤  coset count
    filter_upwards [Filter.eventually_ge_atTop ‖v‖, Filter.eventually_gt_atTop (0 : ℝ)]
      with R hRv hR0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + -‖v‖) ^ 2} ∩ (L : Set ℂ))
        ⊆ {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖v + l‖ ^ 2 ≤ R ^ 2} := by
      rintro x ⟨⟨_, hn⟩, hxL⟩
      refine ⟨hxL, ?_⟩
      have hx : ‖x‖ ≤ R - ‖v‖ := by
        rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ R - ‖v‖)]
        exact Real.sqrt_le_sqrt (by rw [show R + -‖v‖ = R - ‖v‖ from by ring] at hn; exact hn)
      have hvx : ‖v + x‖ ≤ R := le_trans (norm_add_le v x) (by linarith)
      nlinarith [norm_nonneg (v + x)]
    exact_mod_cast Nat.card_mono (hcosetfin R) hsub
  · -- upper: coset count  ≤  count at radius `R + ‖v‖`
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖v + l‖ ^ 2 ≤ R ^ 2}
        ⊆ ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + ‖v‖) ^ 2} ∩ (L : Set ℂ)) := by
      rintro l ⟨hlL, hln⟩
      refine ⟨⟨trivial, ?_⟩, hlL⟩
      have hvl : ‖v + l‖ ≤ R := by
        rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hR0.le]
        exact Real.sqrt_le_sqrt hln
      have hl : ‖l‖ ≤ R + ‖v‖ := by
        calc ‖l‖ = ‖v + l - v‖ := by ring_nf
          _ ≤ ‖v + l‖ + ‖v‖ := norm_sub_le _ _
          _ ≤ R + ‖v‖ := by linarith
      nlinarith [norm_nonneg l, norm_nonneg v]
    exact_mod_cast Nat.card_mono (lattice_span_in_ball_finite hΩ ((R + ‖v‖) ^ 2)) hsub

/-- **Verified — reparametrized coset count.**  The coset analog of `count_reparam_shift`: shifting
the disk radius by a constant `k` leaves the leading coset density unchanged. -/
theorem coset_count_reparam {Ω : ℂ} (hΩ : 0 < Ω.im) (k : ℝ) :
    Filter.Tendsto (fun R : ℝ =>
      (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + k) ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  have hFshift := (theta_coset_disk_count hΩ).comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop k Filter.tendsto_id)
  have hratio : Filter.Tendsto (fun R : ℝ => (R + k) ^ 2 / R ^ 2) Filter.atTop (nhds 1) := by
    have hkR : Filter.Tendsto (fun R : ℝ => k / R) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h1 : Filter.Tendsto (fun R : ℝ => (1 + k / R) ^ 2) Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun R : ℝ => 1 + k / R) Filter.atTop (nhds 1) := by
        simpa using hkR.const_add 1
      simpa using h0.pow 2
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    field_simp
  have hmul := hFshift.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 0 (-k))] with R hR
  have hR0 : 0 < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRk : R + k ≠ 0 := by
    have : -k < R := lt_of_le_of_lt (le_max_right _ _) hR
    linarith
  simp only [Function.comp_apply, id_eq]
  rw [div_mul_div_cancel₀]
  exact pow_ne_zero 2 hRk

/-- **Verified — closed coset disk is finite.** -/
theorem coset_closed_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (R : ℝ) :
    ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
      {z : ℂ | ∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ).Finite := by
  refine (lattice_in_ball_finite hΩ (|R| + 1)).subset ?_
  rintro x ⟨⟨_, hn⟩, m, n, rfl⟩
  refine ⟨⟨m, n, rfl⟩, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : ‖(1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω‖ ≤ |R| := by
    rw [← Real.sqrt_sq (abs_nonneg R), ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (le_trans hn (by rw [sq_abs]))
  linarith

/-- **Verified — a general coset `c + ℤ + Ωℤ` meets any disk in finitely many points.**  Via the
`ZLattice` finiteness (`lattice_span_in_ball_finite`), independent of whether the coset is the zero
set — needed for the *second* coset `z + L` in the matching argument (d). -/
theorem shifted_coset_in_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) (r : ℝ) :
    {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}.Finite := by
  apply Set.Finite.subset
    ((lattice_span_in_ball_finite hΩ ((r + ‖c‖) ^ 2)).image (fun l => c + l))
  rintro u ⟨⟨m, n, rfl⟩, hlt⟩
  refine ⟨(m : ℂ) + (n : ℂ) * Ω, ⟨⟨trivial, ?_⟩, mem_lattice_span_iff.mpr ⟨m, n, rfl⟩⟩,
    by ring⟩
  have hlt' : ‖c + ((m : ℂ) + (n : ℂ) * Ω)‖ < r := by
    rw [show c + ((m : ℂ) + (n : ℂ) * Ω) = c + (m : ℂ) + (n : ℂ) * Ω from by ring]; exact hlt
  have hb : ‖(m : ℂ) + (n : ℂ) * Ω‖ ≤ r + ‖c‖ := by
    calc ‖(m : ℂ) + (n : ℂ) * Ω‖ = ‖(c + ((m : ℂ) + (n : ℂ) * Ω)) - c‖ := by ring_nf
      _ ≤ ‖c + ((m : ℂ) + (n : ℂ) * Ω)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ r + ‖c‖ := by linarith
  nlinarith [norm_nonneg ((m : ℂ) + (n : ℂ) * Ω), norm_nonneg c]

/-- **Verified — coset points are nonzero.**  A half-period-coset point `(1+Ω)/2 + m + nΩ` cannot be
`0`, else `(1+Ω)/2` would lie in the lattice, contradicting `half_period_not_lattice`. -/
theorem coset_ne_zero {Ω : ℂ} (hΩ : 0 < Ω.im) {u : ℂ}
    (h : ∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) : u ≠ 0 := by
  rintro rfl
  obtain ⟨m, n, hu⟩ := h
  exact half_period_not_lattice hΩ ⟨-m, -n, by push_cast; linear_combination -hu⟩

/-- **Verified — open-ball coset count.**  Same leading density with the open condition `‖u‖ < r`
(needed to feed the finite sum↔integral swap): `#{coset points with ‖u‖ < r}/r² → π/Im Ω`. -/
theorem theta_coset_count_open {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun r : ℝ =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (coset_count_reparam hΩ (-1)) (theta_coset_disk_count hΩ) ?_ ?_
  · -- lower: closed count at radius (r-1) ≤ open count at r
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (0 : ℝ)]
      with r hr1 hr0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (r + -1) ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω})
        ⊆ {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} := by
      rintro x ⟨⟨_, hn⟩, hcos⟩
      refine ⟨hcos, ?_⟩
      have : ‖x‖ ≤ r - 1 := by
        rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (by linarith : (0:ℝ) ≤ r - 1)]
        exact Real.sqrt_le_sqrt (by rw [show r + -1 = r - 1 from by ring] at hn; exact hn)
      linarith
    exact_mod_cast Nat.card_mono
      (Set.Finite.subset (lattice_in_ball_finite hΩ r) (fun u hu => ⟨hu.1, by
        rw [Metric.mem_ball, dist_zero_right]; exact hu.2⟩)) hsub
  · -- upper: open count at r ≤ closed count at r
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
        ⊆ ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ r ^ 2} ∩
          {z : ℂ | ∃ m n : ℤ, z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω}) := by
      rintro u ⟨hcos, hlt⟩
      exact ⟨⟨trivial, by nlinarith [norm_nonneg u, hlt.le]⟩, hcos⟩
    exact_mod_cast Nat.card_mono (coset_closed_ball_finite hΩ r) hsub

/-- **Verified — `R²`-normalized Cesàro (null case).**  If `h(r)/r → 0`, then `(∫₀ᴿ h)/R² → 0`.
The engine for the log-weighted asymptotic: from the disk-count limit `N(r)/r² → π/Im Ω` it gives
`(∫₀ᴿ N(r)/r dr)/R² → π/(2 Im Ω)`. -/
theorem tendsto_integral_div_sq_atTop_zero {h : ℝ → ℝ}
    (hh_int : ∀ C : ℝ, IntervalIntegrable h MeasureTheory.volume 0 C)
    (hh : Filter.Tendsto (fun r => h r / r) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun R => (∫ r in (0:ℝ)..R, h r) / R ^ 2) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]; intro ε hε
  rw [Metric.tendsto_atTop] at hh
  obtain ⟨M, hM⟩ := hh (ε / 2) (by linarith)
  set M0 : ℝ := max M 1 with hM0def
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := |∫ r in (0:ℝ)..M0, h r| with hKdef
  have hKnn : 0 ≤ K := abs_nonneg _
  refine ⟨max M0 (Real.sqrt (4 * K / ε) + 1), fun R hR => ?_⟩
  have hRM0 : M0 ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le hM0pos hRM0
  have hRbig : Real.sqrt (4 * K / ε) + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hsub : Set.uIcc M0 R ⊆ Set.uIcc (0:ℝ) R := by
    rw [Set.uIcc_of_le hRM0, Set.uIcc_of_le hRpos.le]; exact Set.Icc_subset_Icc_left hM0pos.le
  have hintMR : IntervalIntegrable h MeasureTheory.volume M0 R := (hh_int R).mono_set hsub
  have hsplit : (∫ r in (0:ℝ)..R, h r) = (∫ r in (0:ℝ)..M0, h r) + (∫ r in M0..R, h r) :=
    (intervalIntegral.integral_add_adjacent_intervals (hh_int M0) hintMR).symm
  have hgint : IntervalIntegrable (fun r => (ε / 2) * r) MeasureTheory.volume M0 R :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hgval : (∫ r in M0..R, (ε / 2) * r) = (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  have htail : |∫ r in M0..R, h r| ≤ (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2) := by
    rw [← hgval]
    have hb := intervalIntegral.norm_integral_le_of_norm_le (f := h) (g := fun r => (ε / 2) * r)
      hRM0 (Filter.Eventually.of_forall (fun t ht => ?_)) hgint
    · rwa [Real.norm_eq_abs] at hb
    · have htpos : 0 < t := lt_of_lt_of_le hM0pos (le_of_lt ht.1)
      have htM : M ≤ t := le_trans (le_max_left _ _) (le_of_lt ht.1)
      have hlt : |h t / t| < ε / 2 := by
        have := hM t htM; simp only [Real.dist_eq, sub_zero] at this; exact this
      rw [abs_div, abs_of_pos htpos] at hlt
      rw [Real.norm_eq_abs]
      exact le_of_lt ((div_lt_iff₀ htpos).mp hlt)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < R ^ 2)]
  have hnum : |∫ r in (0:ℝ)..R, h r| ≤ K + (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2) := by
    rw [hsplit]; exact le_trans (abs_add_le _ _) (by rw [← hKdef]; linarith [htail])
  have hKR : K / R ^ 2 < ε / 2 := by
    rcases eq_or_lt_of_le hKnn with hK0 | hK0
    · rw [← hK0, zero_div]; linarith
    · rw [div_lt_iff₀ (by positivity)]
      have h4 : 4 * K / ε < R ^ 2 := by
        have hsq : Real.sqrt (4 * K / ε) < R := by linarith
        nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * K / ε), Real.sqrt_nonneg (4 * K / ε)]
      rw [div_lt_iff₀ hε] at h4; nlinarith
  calc |∫ r in (0:ℝ)..R, h r| / R ^ 2
      ≤ (K + (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2)) / R ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = K / R ^ 2 + (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2) / R ^ 2 := by ring
    _ < ε := by
        have ht1 : (ε / 2) * ((R ^ 2 - M0 ^ 2) / 2) / R ^ 2 ≤ ε / 4 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg M0, hε.le]
        linarith [hKR]

/-- **Verified — `R²`-normalized Cesàro.**  If `f(r)/r → 2L`, then `(∫₀ᴿ f)/R² → L`. -/
theorem tendsto_integral_div_sq_atTop {f : ℝ → ℝ} {L : ℝ}
    (hf_int : ∀ C : ℝ, IntervalIntegrable f MeasureTheory.volume 0 C)
    (hf : Filter.Tendsto (fun r => f r / r) Filter.atTop (nhds (2 * L))) :
    Filter.Tendsto (fun R => (∫ r in (0:ℝ)..R, f r) / R ^ 2) Filter.atTop (nhds L) := by
  have hh : Filter.Tendsto (fun r => (fun r => f r - 2 * L * r) r / r) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun r => f r / r - 2 * L) Filter.atTop (nhds 0) := by
      simpa using hf.sub_const (2 * L)
    refine h0.congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with r hr
    field_simp
  have hg2 : ∀ C : ℝ, IntervalIntegrable (fun r => 2 * L * r) MeasureTheory.volume 0 C :=
    fun C => (Continuous.intervalIntegrable (by fun_prop) 0 C)
  have hres := tendsto_integral_div_sq_atTop_zero (h := fun r => f r - 2 * L * r)
    (fun C => (hf_int C).sub (hg2 C)) hh
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      (∫ r in (0:ℝ)..R, (f r - 2 * L * r)) / R ^ 2 = (∫ r in (0:ℝ)..R, f r) / R ^ 2 - L := by
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    rw [intervalIntegral.integral_sub (hf_int R) (hg2 R),
      show (∫ r in (0:ℝ)..R, 2 * L * r) = L * R ^ 2 from by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring]
    field_simp
  have hlim := (hres.congr' hev).add_const L
  simpa using hlim

/-- **Verified — step-function primitive of `1/r`.**  `∫₀ᴿ 𝟙[r > a]·r⁻¹ = log(R/a)` for `0 < a ≤ R`.
The pointwise identity behind the Abel/Tonelli step (b): summing this over lattice points `u` (with
`a = ‖u‖`) and swapping the finite sum with the integral turns `Σ log(R/‖u‖)` into `∫₀ᴿ N(r)/r dr`. -/
theorem integral_step_inv {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ∫ r in (0:ℝ)..R, (if a < r then r⁻¹ else 0) = Real.log (R / a) := by
  have hinvR : IntervalIntegrable (fun r => r⁻¹) MeasureTheory.volume a R :=
    (ContinuousOn.inv₀ continuousOn_id (fun x hx => by
      rw [Set.uIcc_of_le haR] at hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1))).intervalIntegrable
  have hint0a : IntervalIntegrable (fun r => if a < r then r⁻¹ else 0) MeasureTheory.volume 0 a := by
    apply (intervalIntegrable_const (c := (0:ℝ))).congr
    intro r hr; rw [Set.uIoc_of_le ha.le] at hr; simp [not_lt.mpr hr.2]
  have hintaR : IntervalIntegrable (fun r => if a < r then r⁻¹ else 0) MeasureTheory.volume a R := by
    apply hinvR.congr
    intro r hr; rw [Set.uIoc_of_le haR] at hr; simp [hr.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint0a hintaR]
  have e1 : (∫ r in (0:ℝ)..a, (if a < r then r⁻¹ else 0)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    intro r hr; rw [Set.uIcc_of_le ha.le] at hr; simp [not_lt.mpr hr.2]
  have e2 : (∫ r in a..R, (if a < r then r⁻¹ else 0)) = Real.log (R / a) := by
    rw [intervalIntegral.integral_congr_ae (g := fun r => r⁻¹) ?_,
      integral_inv_of_pos ha (ha.trans_le haR)]
    filter_upwards with r hr; rw [Set.uIoc_of_le haR] at hr; simp [hr.1]
  rw [e1, e2, zero_add]

/-- **Verified — the step function `𝟙[r>a]·r⁻¹` is interval-integrable on `[0,R]`.** -/
theorem step_inv_intervalIntegrable {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    IntervalIntegrable (fun r => if a < r then r⁻¹ else 0) MeasureTheory.volume 0 R := by
  have hinvR : IntervalIntegrable (fun r => r⁻¹) MeasureTheory.volume a R :=
    (ContinuousOn.inv₀ continuousOn_id (fun x hx => by
      rw [Set.uIcc_of_le haR] at hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1))).intervalIntegrable
  have hint0a : IntervalIntegrable (fun r => if a < r then r⁻¹ else 0) MeasureTheory.volume 0 a := by
    apply (intervalIntegrable_const (c := (0:ℝ))).congr
    intro r hr; rw [Set.uIoc_of_le ha.le] at hr; simp [not_lt.mpr hr.2]
  have hintaR : IntervalIntegrable (fun r => if a < r then r⁻¹ else 0) MeasureTheory.volume a R := by
    apply hinvR.congr
    intro r hr; rw [Set.uIoc_of_le haR] at hr; simp [hr.1]
  exact hint0a.trans hintaR

/-- **Verified — Abel/Tonelli step (finite version).**  For a finite set `T` of points all with
`0 < ‖u‖ ≤ R`, the log-sum equals the integral of the radial counting function:
`∑_{u∈T} log(R/‖u‖) = ∫₀ᴿ (#{u∈T : ‖u‖ < r})/r dr`.  Combined with `theta_coset_disk_count` (a′)
and the continuous Cesàro mean (c), this yields the `~πR²/(2 Im Ω)` log-weighted asymptotic. -/
theorem sum_log_eq_integral_count {T : Finset ℂ} {R : ℝ}
    (hT : ∀ u ∈ T, 0 < ‖u‖ ∧ ‖u‖ ≤ R) :
    ∑ u ∈ T, Real.log (R / ‖u‖)
      = ∫ r in (0:ℝ)..R, (↑(T.filter (fun u => ‖u‖ < r)).card : ℝ) / r := by
  calc ∑ u ∈ T, Real.log (R / ‖u‖)
      = ∑ u ∈ T, ∫ r in (0:ℝ)..R, (if ‖u‖ < r then r⁻¹ else 0) := by
        apply Finset.sum_congr rfl; intro u hu
        rw [integral_step_inv (hT u hu).1 (hT u hu).2]
    _ = ∫ r in (0:ℝ)..R, ∑ u ∈ T, (if ‖u‖ < r then r⁻¹ else 0) := by
        rw [intervalIntegral.integral_finsetSum]
        intro u hu; exact step_inv_intervalIntegrable (hT u hu).1 (hT u hu).2
    _ = ∫ r in (0:ℝ)..R, (↑(T.filter (fun u => ‖u‖ < r)).card : ℝ) / r := by
        apply intervalIntegral.integral_congr
        intro r _
        show (∑ u ∈ T, if ‖u‖ < r then r⁻¹ else 0) = (↑(T.filter (fun u => ‖u‖ < r)).card : ℝ) / r
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          div_eq_mul_inv]

/-- **Verified — the radial coset counting integrand `Ncoset(r)/r` is interval-integrable.**  On
`[0,C]` it agrees with the finite sum `∑_{u∈T} 𝟙[r>‖u‖]·r⁻¹` (`T` = coset points in the disk), each
term integrable by `step_inv_intervalIntegrable`; the counting function matches the Finset filter
count for `r ≤ C`. -/
theorem ncoset_div_intervalIntegrable {Ω : ℂ} (hΩ : 0 < Ω.im) {C : ℝ} (hC : 0 < C) :
    IntervalIntegrable (fun r =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r)
      MeasureTheory.volume 0 C := by
  classical
  set T := (lattice_in_ball_finite hΩ C).toFinset with hT
  have hmem : ∀ u ∈ T, (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < C := by
    intro u hu
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] at hu
    exact hu
  have hsum : IntervalIntegrable
      (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) MeasureTheory.volume 0 C := by
    apply IntervalIntegrable.sum T
    intro u hu
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (coset_ne_zero hΩ (hmem u hu).1)
    exact step_inv_intervalIntegrable hu0 (hmem u hu).2.le
  refine hsum.congr ?_
  intro r hr
  rw [Set.uIoc_of_le hC.le] at hr
  have hset : {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset, Metric.mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨hc, hlt⟩; exact ⟨⟨hc, lt_of_lt_of_le hlt hr.2⟩, hlt⟩
    · rintro ⟨⟨hc, _⟩, hlt⟩; exact ⟨hc, hlt⟩
  have hcard : (Nat.card {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ)
      = ((T.filter (fun u => ‖u‖ < r)).card : ℝ) := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  show (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) r
      = (Nat.card {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r
  rw [Finset.sum_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, ← div_eq_mul_inv, hcard]

/-- **Verified — per-coset log-sum integral asymptotic (culmination of the Abel/Tonelli step).**
`(∫₀ᴿ Ncoset(r)/r dr) / R² → π/(2 Im Ω)`: feeding the radial coset count `Ncoset(r)/r` into the
`R²`-Cesàro mean (its `/r` is `Ncoset(r)/r² → π/Im Ω` by `theta_coset_count_open`).  Combined with
`sum_log_eq_integral_count` this gives the half-period coset's log-weighted density. -/
theorem theta_coset_logsum_integral_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun R : ℝ =>
      (∫ r in (0:ℝ)..R,
        (Nat.card {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r)
        / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  apply tendsto_integral_div_sq_atTop
  · intro C
    rcases lt_or_ge 0 C with hC | hC
    · exact ncoset_div_intervalIntegrable hΩ hC
    · apply (intervalIntegrable_const (c := (0:ℝ))).congr
      intro r hr
      have hr0 : r ≤ 0 := by
        rcases Set.mem_uIoc.mp hr with ⟨h1, h2⟩ | ⟨_, h2⟩
        · linarith
        · exact h2
      have hempty : {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hlt
        exact absurd (lt_of_le_of_lt (norm_nonneg u) hlt) (not_lt.mpr hr0)
      simp [hempty]
  · rw [show (2 : ℝ) * (Real.pi / (2 * Ω.im)) = Real.pi / Ω.im from by ring]
    refine (theta_coset_count_open hΩ).congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with r _
    rw [div_div, pow_two]

/-- **Verified — the half-period coset log-sum has density `π/(2 Im Ω)`.**  For the coset points
`u` in the disk of radius `R`, `(∑_u log(R/‖u‖))/R² → π/(2 Im Ω)`.  This is the per-coset
log-weighted asymptotic that the matching argument (d) plays against the Jensen bound: two distinct
cosets of zeros would contribute `~πR²/Im Ω`, exceeding the Jensen budget `~πR²/(2 Im Ω)`. -/
theorem theta_coset_logsum_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun R : ℝ =>
      (∑ u ∈ (lattice_in_ball_finite hΩ R).toFinset, Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  classical
  refine (theta_coset_logsum_integral_asymptotic hΩ).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with R hR
  set T := (lattice_in_ball_finite hΩ R).toFinset with hT
  have hmem : ∀ u ∈ T, (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < R := by
    intro u hu
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] at hu
    exact hu
  have hsumlog := sum_log_eq_integral_count (T := T) (R := R)
    (fun u hu => ⟨norm_pos_iff.mpr (coset_ne_zero hΩ (hmem u hu).1), (hmem u hu).2.le⟩)
  congr 1
  rw [hsumlog]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hR.le] at hr
  congr 1
  have hset : {u : ℂ | (∃ m n : ℤ, u = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset, Metric.mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨hc, hlt⟩; exact ⟨⟨hc, lt_of_lt_of_le hlt hr.2⟩, hlt⟩
    · rintro ⟨⟨hc, _⟩, hlt⟩; exact ⟨hc, hlt⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **Verified — general-coset disk count.**  For ANY translate `c + ℤ + Ωℤ`, the disk count has the
same leading density `π/Im Ω` (the half-period `theta_coset_disk_count` generalized to arbitrary `c`;
the proof is translation-generic).  Needed for the *second* coset in the matching argument (d). -/
theorem theta_shifted_disk_count {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) :
    Filter.Tendsto (fun R : ℝ =>
      (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  set L := Submodule.span ℤ (Set.range ![(1 : ℂ), Ω]) with hLdef
  have hbij : ∀ R : ℝ,
      Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ)
      = Nat.card {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖c + l‖ ^ 2 ≤ R ^ 2} := by
    intro R
    have hset : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ)
        = (fun l => c + l) '' {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖c + l‖ ^ 2 ≤ R ^ 2} := by
      ext x
      constructor
      · rintro ⟨⟨_, hnorm⟩, m, n, rfl⟩
        refine ⟨(m : ℂ) + (n : ℂ) * Ω, ⟨mem_lattice_span_iff.mpr ⟨m, n, rfl⟩, ?_⟩, by ring⟩
        rw [show c + ((m : ℂ) + (n : ℂ) * Ω) = c + (m : ℂ) + (n : ℂ) * Ω from by ring]
        exact hnorm
      · rintro ⟨l, ⟨hlL, hlnorm⟩, rfl⟩
        obtain ⟨m, n, rfl⟩ := mem_lattice_span_iff.mp hlL
        exact ⟨⟨trivial, hlnorm⟩, m, n, by ring⟩
    rw [hset, Nat.card_image_of_injective (add_right_injective c)]
  have hcosetfin : ∀ R : ℝ, {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖c + l‖ ^ 2 ≤ R ^ 2}.Finite := by
    intro R
    refine (lattice_span_in_ball_finite hΩ ((|R| + ‖c‖) ^ 2)).subset ?_
    rintro l ⟨hlL, hln⟩
    refine ⟨⟨trivial, ?_⟩, hlL⟩
    have h1 : ‖c + l‖ ≤ |R| := by
      rw [← Real.sqrt_sq (abs_nonneg R), ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (le_trans hln (by rw [sq_abs]))
    have h2 : ‖l‖ ≤ |R| + ‖c‖ := by
      calc ‖l‖ = ‖c + l - c‖ := by ring_nf
        _ ≤ ‖c + l‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ |R| + ‖c‖ := by linarith
    nlinarith [norm_nonneg l, norm_nonneg c, abs_nonneg R]
  simp only [hbij]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (count_reparam_shift hΩ (-‖c‖)) (count_reparam_shift hΩ ‖c‖) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop ‖c‖, Filter.eventually_gt_atTop (0 : ℝ)]
      with R hRv hR0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + -‖c‖) ^ 2} ∩ (L : Set ℂ))
        ⊆ {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖c + l‖ ^ 2 ≤ R ^ 2} := by
      rintro x ⟨⟨_, hn⟩, hxL⟩
      refine ⟨hxL, ?_⟩
      have hx : ‖x‖ ≤ R - ‖c‖ := by
        rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ R - ‖c‖)]
        exact Real.sqrt_le_sqrt (by rw [show R + -‖c‖ = R - ‖c‖ from by ring] at hn; exact hn)
      have hvx : ‖c + x‖ ≤ R := le_trans (norm_add_le c x) (by linarith)
      nlinarith [norm_nonneg (c + x)]
    exact_mod_cast Nat.card_mono (hcosetfin R) hsub
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : {l : ℂ | l ∈ (L : Set ℂ) ∧ ‖c + l‖ ^ 2 ≤ R ^ 2}
        ⊆ ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + ‖c‖) ^ 2} ∩ (L : Set ℂ)) := by
      rintro l ⟨hlL, hln⟩
      refine ⟨⟨trivial, ?_⟩, hlL⟩
      have hvl : ‖c + l‖ ≤ R := by
        rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hR0.le]
        exact Real.sqrt_le_sqrt hln
      have hl : ‖l‖ ≤ R + ‖c‖ := by
        calc ‖l‖ = ‖c + l - c‖ := by ring_nf
          _ ≤ ‖c + l‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ R + ‖c‖ := by linarith
      nlinarith [norm_nonneg l, norm_nonneg c]
    exact_mod_cast Nat.card_mono (lattice_span_in_ball_finite hΩ ((R + ‖c‖) ^ 2)) hsub

/-- **Verified — general-coset reparametrized count.** -/
theorem shifted_count_reparam {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) (k : ℝ) :
    Filter.Tendsto (fun R : ℝ =>
      (Nat.card ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (R + k) ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ) : ℝ) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  have hFshift := (theta_shifted_disk_count hΩ c).comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop k Filter.tendsto_id)
  have hratio : Filter.Tendsto (fun R : ℝ => (R + k) ^ 2 / R ^ 2) Filter.atTop (nhds 1) := by
    have hkR : Filter.Tendsto (fun R : ℝ => k / R) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h1 : Filter.Tendsto (fun R : ℝ => (1 + k / R) ^ 2) Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun R : ℝ => 1 + k / R) Filter.atTop (nhds 1) := by
        simpa using hkR.const_add 1
      simpa using h0.pow 2
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    field_simp
  have hmul := hFshift.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 0 (-k))] with R hR
  have hR0 : 0 < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRk : R + k ≠ 0 := by
    have : -k < R := lt_of_le_of_lt (le_max_right _ _) hR
    linarith
  simp only [Function.comp_apply, id_eq]
  rw [div_mul_div_cancel₀]
  exact pow_ne_zero 2 hRk

/-- **Verified — general-coset closed disk is finite.** -/
theorem shifted_closed_ball_finite {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) (R : ℝ) :
    ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ R ^ 2} ∩
      {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω} : Set ℂ).Finite := by
  refine (shifted_coset_in_ball_finite hΩ c (|R| + 1)).subset ?_
  rintro x ⟨⟨_, hn⟩, m, n, rfl⟩
  refine ⟨⟨m, n, rfl⟩, ?_⟩
  have h1 : ‖c + (m : ℂ) + (n : ℂ) * Ω‖ ≤ |R| := by
    rw [← Real.sqrt_sq (abs_nonneg R), ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (le_trans hn (by rw [sq_abs]))
  linarith

/-- **Verified — general-coset open-ball count.** -/
theorem theta_shifted_count_open {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ) :
    Filter.Tendsto (fun r : ℝ =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (shifted_count_reparam hΩ c (-1)) (theta_shifted_disk_count hΩ c) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (0 : ℝ)]
      with r hr1 hr0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ (r + -1) ^ 2} ∩
        {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω})
        ⊆ {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} := by
      rintro x ⟨⟨_, hn⟩, hcos⟩
      refine ⟨hcos, ?_⟩
      have : ‖x‖ ≤ r - 1 := by
        rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (by linarith : (0:ℝ) ≤ r - 1)]
        exact Real.sqrt_le_sqrt (by rw [show r + -1 = r - 1 from by ring] at hn; exact hn)
      linarith
    exact_mod_cast Nat.card_mono (shifted_coset_in_ball_finite hΩ c r) hsub
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have hsub : {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
        ⊆ ({x : ℂ | x ∈ (Set.univ : Set ℂ) ∧ ‖x‖ ^ 2 ≤ r ^ 2} ∩
          {z : ℂ | ∃ m n : ℤ, z = c + (m : ℂ) + (n : ℂ) * Ω}) := by
      rintro u ⟨hcos, hlt⟩
      exact ⟨⟨trivial, by nlinarith [norm_nonneg u, hlt.le]⟩, hcos⟩
    exact_mod_cast Nat.card_mono (shifted_closed_ball_finite hΩ c r) hsub

/-- **Verified — general-coset radial integrand is interval-integrable** (needs `0 ∉ c+L`). -/
theorem shifted_ncoset_div_intervalIntegrable {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ)
    (hc : ∀ m n : ℤ, c + (m : ℂ) + (n : ℂ) * Ω ≠ 0) {C : ℝ} (hC : 0 < C) :
    IntervalIntegrable (fun r =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r)
      MeasureTheory.volume 0 C := by
  classical
  set T := (shifted_coset_in_ball_finite hΩ c C).toFinset with hT
  have hmem : ∀ u ∈ T, (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < C := by
    intro u hu
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hu
    exact hu
  have hsum : IntervalIntegrable
      (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) MeasureTheory.volume 0 C := by
    apply IntervalIntegrable.sum T
    intro u hu
    obtain ⟨⟨m, n, rfl⟩, hlt⟩ := hmem u hu
    exact step_inv_intervalIntegrable (norm_pos_iff.mpr (hc m n)) hlt.le
  refine hsum.congr ?_
  intro r hr
  rw [Set.uIoc_of_le hC.le] at hr
  have hset : {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hc', hlt⟩; exact ⟨⟨hc', lt_of_lt_of_le hlt hr.2⟩, hlt⟩
    · rintro ⟨⟨hc', _⟩, hlt⟩; exact ⟨hc', hlt⟩
  have hcard : (Nat.card {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ)
      = ((T.filter (fun u => ‖u‖ < r)).card : ℝ) := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  show (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) r
      = (Nat.card {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r
  rw [Finset.sum_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, ← div_eq_mul_inv, hcard]

/-- **Verified — general-coset log-sum integral asymptotic.** -/
theorem theta_shifted_logsum_integral_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ)
    (hc : ∀ m n : ℤ, c + (m : ℂ) + (n : ℂ) * Ω ≠ 0) :
    Filter.Tendsto (fun R : ℝ =>
      (∫ r in (0:ℝ)..R,
        (Nat.card {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r)
        / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  apply tendsto_integral_div_sq_atTop
  · intro C
    rcases lt_or_ge 0 C with hC | hC
    · exact shifted_ncoset_div_intervalIntegrable hΩ c hc hC
    · apply (intervalIntegrable_const (c := (0:ℝ))).congr
      intro r hr
      have hr0 : r ≤ 0 := by
        rcases Set.mem_uIoc.mp hr with ⟨h1, h2⟩ | ⟨_, h2⟩
        · linarith
        · exact h2
      have hempty : {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hlt
        exact absurd (lt_of_le_of_lt (norm_nonneg u) hlt) (not_lt.mpr hr0)
      simp [hempty]
  · rw [show (2 : ℝ) * (Real.pi / (2 * Ω.im)) = Real.pi / Ω.im from by ring]
    refine (theta_shifted_count_open hΩ c).congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with r _
    rw [div_div, pow_two]

/-- **Verified — general-coset log-sum has density `π/(2 Im Ω)`.**  The per-coset log-weighted
asymptotic for ANY translate `c+L` with `0 ∉ c+L`; the *second* coset in the matching argument (d). -/
theorem theta_shifted_logsum_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) (c : ℂ)
    (hc : ∀ m n : ℤ, c + (m : ℂ) + (n : ℂ) * Ω ≠ 0) :
    Filter.Tendsto (fun R : ℝ =>
      (∑ u ∈ (shifted_coset_in_ball_finite hΩ c R).toFinset, Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  classical
  refine (theta_shifted_logsum_integral_asymptotic hΩ c hc).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with R hR
  set T := (shifted_coset_in_ball_finite hΩ c R).toFinset with hT
  have hmem : ∀ u ∈ T, (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < R := by
    intro u hu
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hu
    exact hu
  have hsumlog := sum_log_eq_integral_count (T := T) (R := R)
    (fun u hu => by
      obtain ⟨⟨m, n, rfl⟩, hlt⟩ := hmem u hu
      exact ⟨norm_pos_iff.mpr (hc m n), hlt.le⟩)
  congr 1
  rw [hsumlog]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hR.le] at hr
  congr 1
  have hset : {u : ℂ | (∃ m n : ℤ, u = c + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hc', hlt⟩; exact ⟨⟨hc', lt_of_lt_of_le hlt hr.2⟩, hlt⟩
    · rintro ⟨⟨hc', _⟩, hlt⟩; exact ⟨hc', hlt⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **Verified — coset log-sum ≤ the Jensen weighted finsum.**  Each half-period-coset point in the
disk is a zero with `divisor ≥ 1` and `log(R/‖u‖) ≥ 0`, and every finsum term is nonnegative, so the
finite coset log-sum is dominated by `∑ᶠ divisor·log`.  The lower-bound bridge for the matching (d):
combined with the two-coset version it forces the Jensen budget to be exceeded. -/
theorem logsum_le_finsum {Ω : ℂ} (hΩ : 0 < Ω.im) {R : ℝ} (hR : 0 < R) (S : Finset ℂ)
    (hS : ∀ u ∈ S, jacobiTheta₂ u Ω = 0 ∧ ‖u‖ < R) :
    (∑ u ∈ S, Real.log (R / ‖u‖))
      ≤ ∑ᶠ u, (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) u
            * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
  classical
  set D := divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|) with hD
  set f : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) with hf
  set T := (theta_divisor_closedBall_support_finite hΩ |R|).toFinset with hT
  have hRR : |R| = R := abs_of_pos hR
  have hlog : ∀ u : ℂ, ‖u‖ ≤ R → 0 ≤ Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    intro u hu
    have hnu : ‖(0 : ℂ) - u‖ = ‖u‖ := by rw [zero_sub, norm_neg]
    rcases eq_or_ne ‖u‖ 0 with hz | hz
    · rw [hnu, hz, inv_zero, mul_zero, Real.log_zero]
    · apply Real.log_nonneg
      rw [hnu, ← div_eq_mul_inv, le_div_iff₀ (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz))]
      linarith
  have hf_nonneg : ∀ u, 0 ≤ f u := by
    intro u
    rcases eq_or_ne (D u) 0 with h0 | h0
    · simp [hf, h0]
    · have huC : u ∈ Metric.closedBall (0 : ℂ) |R| := by
        by_contra hc
        exact h0 (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hc)
      have hun : ‖u‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_zero_right, hRR] at huC; exact huC
      exact mul_nonneg (by exact_mod_cast theta_divisor_nonneg hΩ _ u) (hlog u hun)
  have hsupp : Function.support f ⊆ ↑T := by
    rw [hT, Set.Finite.coe_toFinset]
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hDu
    apply hu
    show (↑(D u) : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) = 0
    rw [show (D u : ℤ) = 0 from hDu, Int.cast_zero, zero_mul]
  have hST : S ⊆ T := by
    intro u hu
    obtain ⟨hz, hball⟩ := hS u hu
    have huC : u ∈ Metric.closedBall (0 : ℂ) |R| := by
      rw [Metric.mem_closedBall, dist_zero_right, hRR]; exact hball.le
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
    have hge := theta_divisor_ge_one_of_zero hΩ huC hz
    intro hDu; rw [hDu] at hge; exact absurd hge (by norm_num)
  calc (∑ u ∈ S, Real.log (R / ‖u‖))
      ≤ ∑ u ∈ S, f u := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨hz, hball⟩ := hS u hu
        have huC : u ∈ Metric.closedBall (0 : ℂ) |R| := by
          rw [Metric.mem_closedBall, dist_zero_right, hRR]; exact hball.le
        have hd1 : (1 : ℝ) ≤ (D u : ℝ) := by
          exact_mod_cast theta_divisor_ge_one_of_zero hΩ huC hz
        show Real.log (R / ‖u‖) ≤ (↑(D u) : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)
        have harg : R * ‖(0 : ℂ) - u‖⁻¹ = R / ‖u‖ := by rw [zero_sub, norm_neg]; ring
        rw [harg]
        exact le_mul_of_one_le_left (harg ▸ hlog _ hball.le) hd1
    _ ≤ ∑ᶠ u, f u := by
        rw [finsum_eq_finsetSum_of_support_subset f hsupp]
        exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun u _ _ => hf_nonneg u)

/-- **Verified — punctured lattice count.**  The count of *nonzero* lattice points `ℤ + Ωℤ ∖ {0}`
in the disk has the same density `π/Im Ω` (removing the single point `0` is a `1/r² → 0` correction).
Needed for the `z ∈ L` sub-case of the matching argument (where `θ(0)=0` makes `L∖{0}` the second
coset). -/
theorem theta_punctured_count_open {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun r : ℝ =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0} : ℝ)
        / r ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
  have h1r2 : Filter.Tendsto (fun r : ℝ => (1 : ℝ) / r ^ 2) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (Filter.tendsto_pow_atTop two_ne_zero)
  have hmain := (theta_shifted_count_open hΩ 0).sub h1r2
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have h0mem : (0 : ℂ) ∈ {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} := by
    refine ⟨⟨0, 0, by push_cast; ring⟩, ?_⟩; simpa using hr
  have hsetp : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
      = {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} \ {(0 : ℂ)} := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]; tauto
  have hfin : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}.Finite :=
    shifted_coset_in_ball_finite hΩ 0 r
  have hcard : (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
      : ℝ) = (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ)
        - 1 := by
    rw [hsetp, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem h0mem, Nat.card_coe_set_eq]
    have hpos : 1 ≤ {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r}.ncard :=
      (Set.ncard_pos hfin).mpr ⟨0, h0mem⟩
    rw [Nat.cast_sub hpos, Nat.cast_one]
  show (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r} : ℝ) / r ^ 2
      - 1 / r ^ 2
    = (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0} : ℝ)
        / r ^ 2
  rw [hcard]; ring

/-- **Verified — punctured radial integrand is interval-integrable.** -/
theorem punctured_ncoset_div_intervalIntegrable {Ω : ℂ} (hΩ : 0 < Ω.im) {C : ℝ} (hC : 0 < C) :
    IntervalIntegrable (fun r =>
      (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0} : ℝ)
        / r) MeasureTheory.volume 0 C := by
  classical
  have hfinC : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < C ∧ u ≠ 0}.Finite :=
    (shifted_coset_in_ball_finite hΩ 0 C).subset (fun u hu => ⟨hu.1, hu.2.1⟩)
  set T := hfinC.toFinset with hT
  have hmem : ∀ u ∈ T,
      (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < C ∧ u ≠ 0 := by
    intro u hu; rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hu; exact hu
  have hsum : IntervalIntegrable
      (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) MeasureTheory.volume 0 C := by
    apply IntervalIntegrable.sum T
    intro u hu
    exact step_inv_intervalIntegrable (norm_pos_iff.mpr (hmem u hu).2.2) (hmem u hu).2.1.le
  refine hsum.congr ?_
  intro r hr
  rw [Set.uIoc_of_le hC.le] at hr
  have hset : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hc, hlt, hne⟩; exact ⟨⟨hc, lt_of_lt_of_le hlt hr.2, hne⟩, hlt⟩
    · rintro ⟨⟨hc, _, hne⟩, hlt⟩; exact ⟨hc, hlt, hne⟩
  have hcard : (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
      : ℝ) = ((T.filter (fun u => ‖u‖ < r)).card : ℝ) := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  show (∑ u ∈ T, fun r => (if ‖u‖ < r then r⁻¹ else 0)) r
      = (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0} : ℝ)
        / r
  rw [Finset.sum_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, ← div_eq_mul_inv, hcard]

/-- **Verified — punctured lattice log-sum integral asymptotic.** -/
theorem theta_punctured_logsum_integral_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun R : ℝ =>
      (∫ r in (0:ℝ)..R,
        (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0} : ℝ)
          / r) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  apply tendsto_integral_div_sq_atTop
  · intro C
    rcases lt_or_ge 0 C with hC | hC
    · exact punctured_ncoset_div_intervalIntegrable hΩ hC
    · apply (intervalIntegrable_const (c := (0:ℝ))).congr
      intro r hr
      have hr0 : r ≤ 0 := by
        rcases Set.mem_uIoc.mp hr with ⟨h1, h2⟩ | ⟨_, h2⟩
        · linarith
        · exact h2
      have hempty : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
          = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hlt, _⟩
        exact absurd (lt_of_le_of_lt (norm_nonneg u) hlt) (not_lt.mpr hr0)
      show (0 : ℝ) = (Nat.card {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧
        ‖u‖ < r ∧ u ≠ 0} : ℝ) / r
      rw [hempty]; simp
  · rw [show (2 : ℝ) * (Real.pi / (2 * Ω.im)) = Real.pi / Ω.im from by ring]
    refine (theta_punctured_count_open hΩ).congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with r _
    rw [div_div, pow_two]

/-- **Verified — punctured lattice log-sum has density `π/(2 Im Ω)`.**  The nonzero lattice points
carry the full coset density; the second coset for the `z ∈ L` sub-case of (d). -/
theorem theta_punctured_logsum_asymptotic {Ω : ℂ} (hΩ : 0 < Ω.im) :
    Filter.Tendsto (fun R : ℝ =>
      (∑ u ∈ ((shifted_coset_in_ball_finite hΩ 0 R).subset
        (fun u hu => (⟨hu.1, hu.2.1⟩ : (∃ m n : ℤ, u = (0:ℂ) + (m:ℂ) + (n:ℂ)*Ω) ∧ ‖u‖ < R))
        : {u : ℂ | (∃ m n : ℤ, u = (0:ℂ) + (m:ℂ) + (n:ℂ)*Ω) ∧ ‖u‖ < R ∧ u ≠ 0}.Finite).toFinset,
        Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
  classical
  refine (theta_punctured_logsum_integral_asymptotic hΩ).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with R hR
  set hfinR : {u : ℂ | (∃ m n : ℤ, u = (0:ℂ) + (m:ℂ) + (n:ℂ)*Ω) ∧ ‖u‖ < R ∧ u ≠ 0}.Finite :=
    (shifted_coset_in_ball_finite hΩ 0 R).subset (fun u hu => ⟨hu.1, hu.2.1⟩) with hfinRdef
  set T := hfinR.toFinset with hT
  have hmem : ∀ u ∈ T, (∃ m n : ℤ, u = (0:ℂ) + (m:ℂ) + (n:ℂ)*Ω) ∧ ‖u‖ < R ∧ u ≠ 0 := by
    intro u hu; rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hu; exact hu
  have hsumlog := sum_log_eq_integral_count (T := T) (R := R)
    (fun u hu => ⟨norm_pos_iff.mpr (hmem u hu).2.2, (hmem u hu).2.1.le⟩)
  congr 1
  rw [hsumlog]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hR.le] at hr
  congr 1
  have hset : {u : ℂ | (∃ m n : ℤ, u = (0:ℂ) + (m:ℂ) + (n:ℂ)*Ω) ∧ ‖u‖ < r ∧ u ≠ 0}
      = ↑(T.filter (fun u => ‖u‖ < r)) := by
    ext u
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hc, hlt, hne⟩; exact ⟨⟨hc, lt_of_lt_of_le hlt hr.2, hne⟩, hlt⟩
    · rintro ⟨⟨hc, _, hne⟩, hlt⟩; exact ⟨hc, hlt, hne⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **Verified — two disjoint cosets of zeros is impossible.**  If `θ` had two disjoint cosets of
zeros, each with log-weighted density `π/(2 Im Ω)`, their combined density `π/Im Ω` would exceed the
Jensen upper bound `~π/(2 Im Ω)` — contradiction.  This is the matching argument (d): the punchline
that forces the zero set to be a single coset. -/
theorem two_coset_contradiction {Ω : ℂ} (hΩ : 0 < Ω.im)
    (S1 S2 : ℝ → Finset ℂ)
    (hS1 : ∀ {R : ℝ}, 0 < R → ∀ u ∈ S1 R, jacobiTheta₂ u Ω = 0 ∧ ‖u‖ < R)
    (hS2 : ∀ {R : ℝ}, 0 < R → ∀ u ∈ S2 R, jacobiTheta₂ u Ω = 0 ∧ ‖u‖ < R)
    (hdisj : ∀ R : ℝ, Disjoint (S1 R) (S2 R))
    (hlim1 : Filter.Tendsto (fun R : ℝ => (∑ u ∈ S1 R, Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))))
    (hlim2 : Filter.Tendsto (fun R : ℝ => (∑ u ∈ S2 R, Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * Ω.im)))) :
    False := by
  set K := Real.log (2 * ∑' n : ℤ, Real.exp (-Real.pi * Ω.im * (n : ℝ) ^ 2))
    - Real.log ‖meromorphicTrailingCoeffAt (fun z => jacobiTheta₂ z Ω) 0‖ with hK
  have hg : Filter.Tendsto (fun R : ℝ => (∑ u ∈ (S1 R ∪ S2 R), Real.log (R / ‖u‖)) / R ^ 2)
      Filter.atTop (nhds (Real.pi / Ω.im)) := by
    have hsum := hlim1.add hlim2
    rw [show Real.pi / (2 * Ω.im) + Real.pi / (2 * Ω.im) = Real.pi / Ω.im from by
      field_simp; ring] at hsum
    refine hsum.congr' ?_
    filter_upwards with R
    rw [Finset.sum_union (hdisj R), add_div]
  have hh : Filter.Tendsto (fun R : ℝ => K / R ^ 2 + Real.pi / (2 * Ω.im))
      Filter.atTop (nhds (Real.pi / (2 * Ω.im))) := by
    have h0 : Filter.Tendsto (fun R : ℝ => K / R ^ 2) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds (Filter.tendsto_pow_atTop two_ne_zero)
    simpa using h0.add_const (Real.pi / (2 * Ω.im))
  have hgh : ∀ᶠ R : ℝ in Filter.atTop,
      (∑ u ∈ (S1 R ∪ S2 R), Real.log (R / ‖u‖)) / R ^ 2 ≤ K / R ^ 2 + Real.pi / (2 * Ω.im) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR1
    have hR : 0 < R := lt_trans one_pos hR1
    have hle1 := logsum_le_finsum hΩ hR (S1 R ∪ S2 R) (fun u hu => by
      rw [Finset.mem_union] at hu
      rcases hu with h | h
      · exact hS1 hR u h
      · exact hS2 hR u h)
    have hle2 := theta_weighted_count_le hΩ hR
    have hD0 : 0 ≤ (divisor (fun z => jacobiTheta₂ z Ω) (Metric.closedBall (0 : ℂ) |R|)) 0
        * Real.log R := by
      apply mul_nonneg
      · exact_mod_cast theta_divisor_nonneg hΩ _ 0
      · exact Real.log_nonneg hR1.le
    have hpi : Real.pi / Ω.im * (R ^ 2 / 2) = Real.pi / (2 * Ω.im) * R ^ 2 := by field_simp
    rw [div_le_iff₀ (pow_pos hR 2), add_mul, div_mul_cancel₀ K (pow_pos hR 2).ne']
    nlinarith [hle1, hle2, hD0, hpi]
  have hfin := le_of_tendsto_of_tendsto hg hh hgh
  rw [div_le_div_iff₀ hΩ (mul_pos two_pos hΩ)] at hfin
  nlinarith [Real.pi_pos, hΩ, mul_pos Real.pi_pos hΩ]

/-- **Forward direction of the theta zero set** — the fact the Part 5 skeleton imports
as `jacobiTheta₂_mem_of_eq_zero`.  Follows from Residual B: a zero has positive divisor,
so it is a lattice point. -/
theorem jacobiTheta₂_mem_of_eq_zero {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ)
    (h : jacobiTheta₂ z Ω = 0) : ∃ m n : ℤ, z = (1 + Ω) / 2 + m + n * Ω := by
  classical
  by_contra hz
  -- `hS1`: the half-period coset supplies zeros of `θ` inside the ball.
  have hS1 : ∀ {R : ℝ}, 0 < R → ∀ u ∈ (lattice_in_ball_finite hΩ R).toFinset,
      jacobiTheta₂ u Ω = 0 ∧ ‖u‖ < R := by
    intro R _ u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨⟨m, n, rfl⟩, hball⟩ := hu
    refine ⟨jacobiTheta₂_eq_zero_at_lattice Ω m n, ?_⟩
    rwa [Metric.mem_ball, dist_zero_right] at hball
  by_cases hzL : ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * Ω
  · -- `z ∈ ℤ + Ω·ℤ`: then `θ 0 = 0`, and the punctured lattice `L ∖ {0}` is a second
    -- coset of zeros disjoint from the half-period coset.
    obtain ⟨m₀, n₀, hz0⟩ := hzL
    have h00 : jacobiTheta₂ 0 Ω = 0 := by
      have ht := jacobiTheta₂_eq_zero_translate h (-m₀) (-n₀)
      rwa [show z + ((-m₀ : ℤ) : ℂ) + ((-n₀ : ℤ) : ℂ) * Ω = 0 from by
        rw [hz0]; push_cast; ring] at ht
    refine two_coset_contradiction hΩ
      (fun R => (lattice_in_ball_finite hΩ R).toFinset)
      (fun R => ((shifted_coset_in_ball_finite hΩ 0 R).subset
          (fun u hu => (⟨hu.1, hu.2.1⟩ :
            (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω) ∧ ‖u‖ < R))
          : {u : ℂ | (∃ m n : ℤ, u = (0 : ℂ) + (m : ℂ) + (n : ℂ) * Ω)
              ∧ ‖u‖ < R ∧ u ≠ 0}.Finite).toFinset)
      hS1 ?_ ?_ (theta_coset_logsum_asymptotic hΩ) (theta_punctured_logsum_asymptotic hΩ)
    · -- `hS2` for the punctured lattice.
      intro R _ u hu
      rw [Set.Finite.mem_toFinset] at hu
      obtain ⟨⟨m, n, rfl⟩, hlt, _⟩ := hu
      exact ⟨jacobiTheta₂_eq_zero_translate h00 m n, hlt⟩
    · -- disjointness: a common point would place the half-period in the lattice.
      intro R
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [Set.Finite.mem_toFinset] at hu1 hu2
      obtain ⟨⟨m, n, rfl⟩, _⟩ := hu1
      obtain ⟨⟨m', n', hu2eq⟩, _, _⟩ := hu2
      exact half_period_not_lattice hΩ ⟨m' - m, n' - n, by push_cast; linear_combination hu2eq⟩
  · -- `z ∉ ℤ + Ω·ℤ`: then `z + L` is a coset of zeros (no point of it is `0`),
    -- disjoint from the half-period coset (else `z` would lie in it).
    have hc : ∀ m n : ℤ, z + (m : ℂ) + (n : ℂ) * Ω ≠ 0 := by
      intro m n heq
      exact hzL ⟨-m, -n, by push_cast; linear_combination heq⟩
    refine two_coset_contradiction hΩ
      (fun R => (lattice_in_ball_finite hΩ R).toFinset)
      (fun R => (shifted_coset_in_ball_finite hΩ z R).toFinset)
      hS1 ?_ ?_ (theta_coset_logsum_asymptotic hΩ) (theta_shifted_logsum_asymptotic hΩ z hc)
    · -- `hS2` for the `z`-coset.
      intro R _ u hu
      rw [Set.Finite.mem_toFinset] at hu
      obtain ⟨⟨m, n, rfl⟩, hlt⟩ := hu
      exact ⟨jacobiTheta₂_eq_zero_translate h m n, hlt⟩
    · -- disjointness: a common point would place `z` in the half-period coset.
      intro R
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [Set.Finite.mem_toFinset] at hu1 hu2
      obtain ⟨⟨m, n, rfl⟩, _⟩ := hu1
      obtain ⟨⟨m', n', hu2eq⟩, _⟩ := hu2
      exact hz ⟨m - m', n - n', by push_cast; linear_combination -hu2eq⟩

/-- **Cell geometry.**  In the fundamental cell (with `ζ = (1+Ω)/2` at its centre), the theta vanishes
*only* at `ζ`: parametrising `w = s + tΩ`, a zero forces `s = t = 1/2` by the theta zero-set (a
half-period lattice coset) and the ℝ-independence of `1, Ω`.  The `(-1/2, 3/2)` range covers an open
neighbourhood of the closed cell `[0,1]²` — this is the "θ ≠ 0 except at the pole" input the
argument-principle contour needs. -/
theorem theta_zero_cell_iff {Ω : ℂ} (hΩ : 0 < Ω.im) (s t : ℝ)
    (hs : s ∈ Set.Ioo (-1/2 : ℝ) (3/2)) (ht : t ∈ Set.Ioo (-1/2 : ℝ) (3/2)) :
    jacobiTheta₂ ((s : ℂ) + (t : ℂ) * Ω) Ω = 0 ↔ (s = 1/2 ∧ t = 1/2) := by
  constructor
  · intro hz
    obtain ⟨m, n, hmn⟩ := jacobiTheta₂_mem_of_eq_zero hΩ _ hz
    have heq : (s : ℂ) + (t : ℂ) * Ω = ((1/2 + (m : ℝ) : ℝ) : ℂ) + ((1/2 + (n : ℝ) : ℝ) : ℂ) * Ω := by
      rw [hmn]; push_cast; ring
    obtain ⟨hsm, htn⟩ := coord_indep_real (ne_of_gt hΩ) s t _ _ heq
    have hm0 : m = 0 := by
      rw [hsm] at hs
      have h1 : (-1:ℤ) < m := by have := hs.1; exact_mod_cast (by linarith : (-1:ℝ) < (m:ℝ))
      have h2 : m < 1 := by have := hs.2; exact_mod_cast (by linarith : (m:ℝ) < 1)
      omega
    have hn0 : n = 0 := by
      rw [htn] at ht
      have h1 : (-1:ℤ) < n := by have := ht.1; exact_mod_cast (by linarith : (-1:ℝ) < (n:ℝ))
      have h2 : n < 1 := by have := ht.2; exact_mod_cast (by linarith : (n:ℝ) < 1)
      omega
    exact ⟨by rw [hsm, hm0]; norm_num, by rw [htn, hn0]; norm_num⟩
  · rintro ⟨rfl, rfl⟩
    rw [show ((1/2:ℝ) : ℂ) + ((1/2:ℝ) : ℂ) * Ω = (1 + Ω)/2 by push_cast; ring]
    exact jacobiTheta₂_half_period_eq_zero Ω

/-- Recover the `(s,t)`-coordinates of `z = s + tΩ`: `t = z.im/Ω.im`, `s = z.re − t·Ω.re`. -/
theorem cell_recover {Ω : ℂ} (hΩ : Ω.im ≠ 0) (z : ℂ) :
    z = ((z.re - z.im / Ω.im * Ω.re : ℝ) : ℂ) + ((z.im / Ω.im : ℝ) : ℂ) * Ω := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    field_simp; ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
      zero_mul, add_zero]
    field_simp

/-- Open neighbourhood of the fundamental cell (in `(s,t)`-coordinates `(-1/2,3/2)²`) — the domain `U`
on which `g = θ'/θ − m/(·−ζ)` is holomorphic (θ vanishes only at the centre `ζ`). -/
def cellNbhd (Ω : ℂ) : Set ℂ :=
  {z | (z.re - z.im / Ω.im * Ω.re) ∈ Set.Ioo (-1/2:ℝ) (3/2) ∧
       z.im / Ω.im ∈ Set.Ioo (-1/2:ℝ) (3/2)}

theorem isOpen_cellNbhd (Ω : ℂ) : IsOpen (cellNbhd Ω) :=
  (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))

/-- The theta is non-vanishing on the open cell neighbourhood except at the centre `ζ = (1+Ω)/2`. -/
theorem theta_ne_zero_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) {z : ℂ}
    (hz : z ∈ cellNbhd Ω) (hzζ : z ≠ (1 + Ω)/2) : jacobiTheta₂ z Ω ≠ 0 := by
  intro h0
  rw [cell_recover (ne_of_gt hΩ) z] at h0
  rw [theta_zero_cell_iff hΩ _ _ hz.1 hz.2] at h0
  apply hzζ
  rw [cell_recover (ne_of_gt hΩ) z, h0.1, h0.2]
  push_cast; ring

/-- **The theta has no real zeros.**  Its zeros `(1+Ω)/2 + m + nΩ` have imaginary part
`(n+1/2)·Ω.im ≠ 0`.  This is the "θ ≠ 0 on the bottom side" input the periodicity contour needs. -/
theorem theta_no_real_zero {Ω : ℂ} (hΩ : 0 < Ω.im) (t : ℝ) : jacobiTheta₂ (t : ℂ) Ω ≠ 0 := by
  intro h
  obtain ⟨m, n, hmn⟩ := jacobiTheta₂_mem_of_eq_zero hΩ _ h
  have him := congrArg Complex.im hmn
  simp only [Complex.ofReal_im, Complex.add_im, Complex.div_im, Complex.one_im, Complex.mul_im,
    Complex.intCast_im, Complex.intCast_re, Complex.add_re, Complex.one_re, Complex.div_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, zero_mul, mul_zero, add_zero,
    zero_add] at him
  have hz : ((2 * (n : ℝ) + 1)) * Ω.im = 0 := by nlinarith [him]
  rcases mul_eq_zero.mp hz with h1 | h2
  · have : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast h1
    omega
  · exact (ne_of_gt hΩ) h2

end LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount
