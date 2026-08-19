import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Towards the residue theorem on a lattice parallelogram

The remaining analytic core of the Frobenius factorization (Abel–Jacobi / sum-of-zeros) reduces to
"an elliptic function of degree `1` is impossible", i.e. a doubly-periodic meromorphic function
cannot have a single simple pole.  The classical proof integrates around a fundamental
parallelogram: the contour integral is `0` by periodicity (opposite sides cancel) yet equals
`2πi·(residue)` by the residue theorem, forcing the residue to be `0`.

This file builds the **periodicity half** of that argument — elementary and infrastructure-free: the
oriented contour integral of a doubly-periodic function around a fundamental parallelogram is `0`.
(The residue half — `∮ = 2πi·res` — needs the parallelogram residue theorem, which Mathlib does not
yet provide.)
-/

namespace LyubarskiiNes.FrobeniusDeterminant.ResidueTheorem

open Complex intervalIntegral Filter
open scoped Topology

/-- The oriented contour integral of `f` around the boundary of the parallelogram with corners
`z₀, z₀+1, z₀+1+c, z₀+c` (bottom, right, top, left; counterclockwise), written as a sum of the four
side integrals with their `dz` factors. -/
noncomputable def parContourIntegral (f : ℂ → ℂ) (z₀ c : ℂ) : ℂ :=
  (∫ t : ℝ in (0)..1, f (z₀ + (t : ℂ)))
    + c * (∫ t : ℝ in (0)..1, f (z₀ + 1 + (t : ℂ) * c))
    - (∫ t : ℝ in (0)..1, f (z₀ + c + (t : ℂ)))
    - c * (∫ t : ℝ in (0)..1, f (z₀ + (t : ℂ) * c))

/-- **Periodicity half of the residue argument.**  If `f` is periodic with periods `1` and `c`,
its contour integral around any fundamental parallelogram is `0`: the right and left sides cancel
(period `1`), and the bottom and top sides cancel (period `c`). -/
theorem parContourIntegral_eq_zero (f : ℂ → ℂ) (z₀ c : ℂ)
    (h1 : Function.Periodic f 1) (hc : Function.Periodic f c) :
    parContourIntegral f z₀ c = 0 := by
  unfold parContourIntegral
  have hright : (∫ t : ℝ in (0)..1, f (z₀ + 1 + (t : ℂ) * c))
      = ∫ t : ℝ in (0)..1, f (z₀ + (t : ℂ) * c) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show z₀ + 1 + (t : ℂ) * c = (z₀ + (t : ℂ) * c) + 1 by ring]
    exact h1 (z₀ + (t : ℂ) * c)
  have htop : (∫ t : ℝ in (0)..1, f (z₀ + c + (t : ℂ)))
      = ∫ t : ℝ in (0)..1, f (z₀ + (t : ℂ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show z₀ + c + (t : ℂ) = (z₀ + (t : ℂ)) + c by ring]
    exact hc (z₀ + (t : ℂ))
  rw [hright, htop]
  ring

/-- Linearity of the contour integral in the integrand: constants pull out. -/
theorem parContourIntegral_const_mul (r : ℂ) (h : ℂ → ℂ) (z₀ c : ℂ) :
    parContourIntegral (fun z => r * h z) z₀ c = r * parContourIntegral h z₀ c := by
  unfold parContourIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Additivity of the contour integral in the integrand (given side-wise integrability). -/
theorem parContourIntegral_split (g h : ℂ → ℂ) (z₀ c : ℂ)
    (Ig1 : IntervalIntegrable (fun t : ℝ => g (z₀ + (t:ℂ))) MeasureTheory.volume 0 1)
    (Ig2 : IntervalIntegrable (fun t : ℝ => g (z₀ + 1 + (t:ℂ) * c)) MeasureTheory.volume 0 1)
    (Ig3 : IntervalIntegrable (fun t : ℝ => g (z₀ + c + (t:ℂ))) MeasureTheory.volume 0 1)
    (Ig4 : IntervalIntegrable (fun t : ℝ => g (z₀ + (t:ℂ) * c)) MeasureTheory.volume 0 1)
    (Ih1 : IntervalIntegrable (fun t : ℝ => h (z₀ + (t:ℂ))) MeasureTheory.volume 0 1)
    (Ih2 : IntervalIntegrable (fun t : ℝ => h (z₀ + 1 + (t:ℂ) * c)) MeasureTheory.volume 0 1)
    (Ih3 : IntervalIntegrable (fun t : ℝ => h (z₀ + c + (t:ℂ))) MeasureTheory.volume 0 1)
    (Ih4 : IntervalIntegrable (fun t : ℝ => h (z₀ + (t:ℂ) * c)) MeasureTheory.volume 0 1) :
    parContourIntegral (fun z => g z + h z) z₀ c
      = parContourIntegral g z₀ c + parContourIntegral h z₀ c := by
  unfold parContourIntegral
  simp only []
  rw [intervalIntegral.integral_add Ig1 Ih1, intervalIntegral.integral_add Ig2 Ih2,
    intervalIntegral.integral_add Ig3 Ih3, intervalIntegral.integral_add Ig4 Ih4]
  ring

/-- **Segment integral of `1/(z−ζ)`.**  Over a segment `t ↦ w₀ + t·v` that stays in the slit plane
(avoids the branch cut `(-∞, 0]`), the integral of `v/(w₀+t·v)` is `log(w₀+v) − log w₀`, since
`Complex.log` is a primitive of `1/·` there.  This is the per-side building block of the winding
integral `∮_∂P 1/(z−ζ)` (whose assembly needs to track the branch jumps that sum to `2πi`). -/
theorem segment_integral_inv (w₀ v : ℂ)
    (hslit : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → w₀ + (t : ℂ) * v ∈ slitPlane) :
    (∫ t : ℝ in (0)..1, v / (w₀ + (t : ℂ) * v)) = Complex.log (w₀ + v) - Complex.log w₀ := by
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => Complex.log (w₀ + (s : ℂ) * v)) (v / (w₀ + (t : ℂ) * v)) t := by
    intro t ht
    have hpath : HasDerivAt (fun s : ℝ => w₀ + (s : ℂ) * v) v t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add w₀
    have h := (Complex.hasDerivAt_log (hslit t ht)).comp_of_eq t hpath rfl
    rw [div_eq_mul_inv, mul_comm]
    exact h
  have hcont : ContinuousOn (fun t : ℝ => v / (w₀ + (t : ℂ) * v)) (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact Complex.slitPlane_ne_zero (hslit t ht)
  rw [integral_eq_sub_of_hasDerivAt key hcont.intervalIntegrable]
  simp

/-- **Rotated segment integral of `1/(z−ζ)`.**  For any nonzero rotation/scaling `u`, if the rotated
segment `t ↦ u·(w₀+t·v)` stays in the slit plane, then `∫ v/(w₀+t·v) = log(u(w₀+v)) − log(u·w₀)`.
This lets each side of the winding contour use whichever branch keeps it off the cut; the branch
choices differ around a loop enclosing `ζ`, and their `log`-value mismatches sum to `2πi` (the
winding number) — the assembly step still to be built. -/
theorem segment_integral_inv_rot (u w₀ v : ℂ) (hu : u ≠ 0)
    (hslit : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → u * (w₀ + (t : ℂ) * v) ∈ slitPlane) :
    (∫ t : ℝ in (0)..1, v / (w₀ + (t : ℂ) * v))
      = Complex.log (u * (w₀ + v)) - Complex.log (u * w₀) := by
  have hslit' : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → u * w₀ + (t : ℂ) * (u * v) ∈ slitPlane := by
    intro t ht
    rw [show u * w₀ + (t : ℂ) * (u * v) = u * (w₀ + (t : ℂ) * v) by ring]
    exact hslit t ht
  have hcongr : (∫ t : ℝ in (0)..1, v / (w₀ + (t : ℂ) * v))
      = ∫ t : ℝ in (0)..1, (u * v) / (u * w₀ + (t : ℂ) * (u * v)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show u * w₀ + (t : ℂ) * (u * v) = u * (w₀ + (t : ℂ) * v) by ring,
      mul_div_mul_left _ _ hu]
  rw [hcongr, segment_integral_inv (u * w₀) (u * v) hslit',
    show u * w₀ + u * v = u * (w₀ + v) by ring]

/-! ### The parallelogram winding number `∮_∂P 1/(z−ζ) = 2πi`

For the fundamental parallelogram **centered at the pole `ζ`** (corners `ζ ± (1±c)/2`), the four
corners land in fixed half-planes *independent of `Re c`*: the bottom/right/top sides stay in the
principal slit plane, only the left side crosses the cut (handled by the `u = -1` rotation), and the
`log`-value mismatches collapse — via `log(-a) - log a = ±πi` — to exactly `2πi`.  This is the
residue half of the parallelogram residue theorem, previously the missing infrastructure. -/

/-- `log(-a) - log a = πi` when `a` is in the (open) lower half-plane. -/
theorem log_neg_sub_log_of_im_neg (a : ℂ) (ha : a.im < 0) :
    Complex.log (-a) - Complex.log a = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.log_re, norm_neg, Complex.mul_re]
  · simp [Complex.sub_im, Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg ha, Complex.mul_im]

/-- `log(-a) - log a = -πi` when `a` is in the (open) upper half-plane. -/
theorem log_neg_sub_log_of_im_pos (a : ℂ) (ha : 0 < a.im) :
    Complex.log (-a) - Complex.log a = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.log_re, norm_neg, Complex.mul_re]
  · simp [Complex.sub_im, Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos ha, Complex.mul_im]

private lemma im_bot (c : ℂ) (t : ℝ) : (-(1+c)/2 + (t:ℂ)*1).im = -(c.im)/2 := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.neg_im, Complex.div_im, Complex.add_re, Complex.one_re,
    Complex.neg_re, Complex.div_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_ofNat]
  ring

private lemma im_top (c : ℂ) (t : ℝ) : ((c-1)/2 + (t:ℂ)*1).im = c.im/2 := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.neg_im, Complex.div_im, Complex.add_re, Complex.one_re,
    Complex.neg_re, Complex.sub_im, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  ring

private lemma im_right (c : ℂ) (t : ℝ) : ((1-c)/2 + (t:ℂ)*c).im = c.im*(t - 1/2) := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.neg_im, Complex.div_im, Complex.add_re, Complex.one_re,
    Complex.neg_re, Complex.sub_im, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  ring

private lemma re_right_half (c : ℂ) : ((1-c)/2 + ((1/2 : ℝ):ℂ)*c).re = 1/2 := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.div_re,
    Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  ring

private lemma im_left (c : ℂ) (t : ℝ) : ((-1:ℂ)*(-(1+c)/2 + (t:ℂ)*c)).im = c.im*(1/2 - t) := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.neg_im, Complex.div_im, Complex.add_re, Complex.one_re,
    Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  ring

private lemma re_left_half (c : ℂ) : ((-1:ℂ)*(-(1+c)/2 + ((1/2:ℝ):ℂ)*c)).re = 1/2 := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.div_re,
    Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  ring

private lemma im_a0 (c : ℂ) : (-(1+c)/2).im = -(c.im)/2 := by
  simp only [Complex.neg_im, Complex.div_im, Complex.add_im, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat, Complex.neg_re, Complex.div_re, Complex.add_re,
    Complex.one_re]
  ring

private lemma im_a3 (c : ℂ) : ((c-1)/2).im = c.im/2 := by
  simp only [Complex.sub_im, Complex.div_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_ofNat, Complex.sub_re, Complex.div_re, Complex.one_re]
  ring

/-- **Parallelogram residue integral / winding number.**  For the fundamental parallelogram centered
at `ζ` (`z₀ = ζ - (1+c)/2`, sides `1` and `c` with `0 < c.im`), the contour integral of `1/(z−ζ)`
equals `2πi`.  Together with `parContourIntegral_eq_zero` (periodicity) and
`parContourIntegral_eq_zero_of_primitive` (Cauchy), this is the parallelogram residue theorem — the
"an elliptic function of degree `1` is impossible" input to the Abel–Jacobi step. -/
theorem parContourIntegral_inv_eq (ζ c : ℂ) (hc : 0 < c.im) :
    parContourIntegral (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2) c = 2 * (Real.pi : ℂ) * I := by
  have hc0 : c.im ≠ 0 := ne_of_gt hc
  have mem_bot : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → (-(1+c)/2 + (t:ℂ)*1) ∈ slitPlane := by
    intro t _; rw [Complex.mem_slitPlane_iff]; right; rw [im_bot]
    exact div_ne_zero (neg_ne_zero.mpr hc0) two_ne_zero
  have mem_top : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → ((c-1)/2 + (t:ℂ)*1) ∈ slitPlane := by
    intro t _; rw [Complex.mem_slitPlane_iff]; right; rw [im_top]
    exact div_ne_zero hc0 two_ne_zero
  have mem_rgt : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → ((1-c)/2 + (t:ℂ)*c) ∈ slitPlane := by
    intro t _; rw [Complex.mem_slitPlane_iff]
    by_cases h : t = 1/2
    · left; subst h; rw [re_right_half]; norm_num
    · right; rw [im_right]; exact mul_ne_zero hc0 (sub_ne_zero.mpr h)
  have mem_lft : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → ((-1:ℂ)*(-(1+c)/2 + (t:ℂ)*c)) ∈ slitPlane := by
    intro t _; rw [Complex.mem_slitPlane_iff]
    by_cases h : t = 1/2
    · left; subst h; rw [re_left_half]; norm_num
    · right; rw [im_left]; exact mul_ne_zero hc0 (sub_ne_zero.mpr (Ne.symm h))
  have hbot : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + (t:ℂ)))
      = Complex.log ((1 - c)/2) - Complex.log (-(1 + c)/2) := by
    have e1 : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + (t:ℂ)))
        = ∫ t : ℝ in (0)..1, (1:ℂ) / (-(1+c)/2 + (t:ℂ)*1) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      show (1:ℂ)/(ζ - (1+c)/2 + (t:ℂ) - ζ) = 1/(-(1+c)/2 + (t:ℂ)*1)
      rw [show ζ - (1+c)/2 + (t:ℂ) - ζ = -(1+c)/2 + (t:ℂ)*1 by ring]
    rw [e1, segment_integral_inv (-(1+c)/2) 1 mem_bot, show -(1+c)/2 + 1 = (1-c)/2 by ring]
  have hrgt : c * (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + 1 + (t:ℂ)*c))
      = Complex.log ((1 + c)/2) - Complex.log ((1 - c)/2) := by
    have e1 : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + 1 + (t:ℂ)*c))
        = ∫ t : ℝ in (0)..1, (1:ℂ) / ((1-c)/2 + (t:ℂ)*c) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      show (1:ℂ)/(ζ - (1+c)/2 + 1 + (t:ℂ)*c - ζ) = 1/((1-c)/2 + (t:ℂ)*c)
      rw [show ζ - (1+c)/2 + 1 + (t:ℂ)*c - ζ = (1-c)/2 + (t:ℂ)*c by ring]
    rw [e1, ← intervalIntegral.integral_const_mul]
    have e2 : (∫ t : ℝ in (0)..1, c * ((1:ℂ) / ((1-c)/2 + (t:ℂ)*c)))
        = ∫ t : ℝ in (0)..1, c / ((1-c)/2 + (t:ℂ)*c) :=
      intervalIntegral.integral_congr (fun t _ => by rw [mul_one_div])
    rw [e2, segment_integral_inv ((1-c)/2) c mem_rgt, show (1-c)/2 + c = (1+c)/2 by ring]
  have htop : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + c + (t:ℂ)))
      = Complex.log ((1 + c)/2) - Complex.log ((c - 1)/2) := by
    have e1 : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + c + (t:ℂ)))
        = ∫ t : ℝ in (0)..1, (1:ℂ) / ((c-1)/2 + (t:ℂ)*1) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      show (1:ℂ)/(ζ - (1+c)/2 + c + (t:ℂ) - ζ) = 1/((c-1)/2 + (t:ℂ)*1)
      rw [show ζ - (1+c)/2 + c + (t:ℂ) - ζ = (c-1)/2 + (t:ℂ)*1 by ring]
    rw [e1, segment_integral_inv ((c-1)/2) 1 mem_top, show (c-1)/2 + 1 = (1+c)/2 by ring]
  have hlft : c * (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + (t:ℂ)*c))
      = Complex.log ((-1:ℂ)*((c-1)/2)) - Complex.log ((-1:ℂ)*(-(1+c)/2)) := by
    have e1 : (∫ t : ℝ in (0)..1, (fun z => 1 / (z - ζ)) (ζ - (1 + c) / 2 + (t:ℂ)*c))
        = ∫ t : ℝ in (0)..1, (1:ℂ) / (-(1+c)/2 + (t:ℂ)*c) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      show (1:ℂ)/(ζ - (1+c)/2 + (t:ℂ)*c - ζ) = 1/(-(1+c)/2 + (t:ℂ)*c)
      rw [show ζ - (1+c)/2 + (t:ℂ)*c - ζ = -(1+c)/2 + (t:ℂ)*c by ring]
    rw [e1, ← intervalIntegral.integral_const_mul]
    have e2 : (∫ t : ℝ in (0)..1, c * ((1:ℂ) / (-(1+c)/2 + (t:ℂ)*c)))
        = ∫ t : ℝ in (0)..1, c / (-(1+c)/2 + (t:ℂ)*c) :=
      intervalIntegral.integral_congr (fun t _ => by rw [mul_one_div])
    rw [e2, segment_integral_inv_rot (-1) (-(1+c)/2) c (by norm_num) mem_lft,
      show -(1+c)/2 + c = (c-1)/2 by ring]
  have h1 : Complex.log (-(-(1+c)/2)) - Complex.log (-(1+c)/2) = (Real.pi:ℂ) * I :=
    log_neg_sub_log_of_im_neg (-(1+c)/2)
      (by rw [im_a0]; exact div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr hc) two_pos)
  have h2 : Complex.log (-((c-1)/2)) - Complex.log ((c-1)/2) = -(Real.pi:ℂ) * I :=
    log_neg_sub_log_of_im_pos ((c-1)/2) (by rw [im_a3]; exact div_pos hc two_pos)
  unfold parContourIntegral
  rw [hbot, hrgt, htop, hlft, neg_one_mul, neg_one_mul]
  linear_combination h1 - h2

/-- **Slanted-side split.**  Splitting a slanted side `c·∫₀¹ g(a+t·c)` at its midpoint (affine
substitutions `t = s/2` and `t = (1+s)/2`): `c·∫ = (c/2)·∫ g(a+s·(c/2)) + (c/2)·∫ g(a+c/2+s·(c/2))`.
The core of the parallelogram-Cauchy subdivision additivity. -/
theorem slant_split (g : ℂ → ℂ) (a c : ℂ)
    (hint : IntervalIntegrable (fun t : ℝ => g (a + (t : ℂ) * c)) MeasureTheory.volume 0 1) :
    c * ∫ t in (0:ℝ)..1, g (a + (t : ℂ) * c)
      = (c / 2) * (∫ s in (0:ℝ)..1, g (a + (s : ℂ) * (c / 2)))
        + (c / 2) * (∫ s in (0:ℝ)..1, g (a + c / 2 + (s : ℂ) * (c / 2))) := by
  have hi1 : IntervalIntegrable (fun t : ℝ => g (a + (t : ℂ) * c)) MeasureTheory.volume 0 (1/2) :=
    hint.mono_set (Set.uIcc_subset_uIcc_iff_le.mpr ⟨by norm_num, by norm_num⟩)
  have hi2 : IntervalIntegrable (fun t : ℝ => g (a + (t : ℂ) * c)) MeasureTheory.volume (1/2) 1 :=
    hint.mono_set (Set.uIcc_subset_uIcc_iff_le.mpr ⟨by norm_num, by norm_num⟩)
  have h1 : (∫ t in (0:ℝ)..(1/2), g (a + (t : ℂ) * c))
      = (1/2 : ℝ) • ∫ s in (0:ℝ)..1, g (a + (s : ℂ) * (c / 2)) := by
    have h := intervalIntegral.integral_comp_div (a := (0:ℝ)) (b := 1)
      (f := fun t : ℝ => g (a + (t : ℂ) * c)) (c := 2) (by norm_num)
    simp only [zero_div] at h
    rw [show (∫ x in (0:ℝ)..1, g (a + (↑(x/2)) * c)) = ∫ s in (0:ℝ)..1, g (a + ↑s * (c / 2)) from
      intervalIntegral.integral_congr (fun x _ => by congr 1; push_cast; ring)] at h
    rw [h, smul_smul]; norm_num
  have h2 : (∫ t in (1/2:ℝ)..1, g (a + (t : ℂ) * c))
      = (1/2 : ℝ) • ∫ s in (0:ℝ)..1, g (a + c / 2 + (s : ℂ) * (c / 2)) := by
    have h := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
      (f := fun t : ℝ => g (a + (t : ℂ) * c)) (c := 1/2) (by norm_num) (1/2)
    rw [show ((1/2:ℝ)*0+1/2) = 1/2 by norm_num, show ((1/2:ℝ)*1+1/2) = 1 by norm_num,
      show ((1/2:ℝ))⁻¹ = 2 by norm_num] at h
    rw [show (∫ x in (0:ℝ)..1, g (a + ↑((1/2)*x + 1/2) * c))
        = ∫ s in (0:ℝ)..1, g (a + c / 2 + ↑s * (c / 2)) from
      intervalIntegral.integral_congr (fun x _ => by congr 1; push_cast; ring)] at h
    rw [h, smul_smul]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2, real_smul, real_smul]
  push_cast; ring

/-! ### General variable-side contour (for both-direction subdivision)

`parContourIntegral` fixes the first side to `1`.  To subdivide a cell in *both* directions (needed
when it is too long-and-thin to fit any single zero-free disk), we use `parContourGen` with both
sides variable, and its two subdivision lemmas `split_a`, `split_c`. -/

/-- Contour integral over the parallelogram with corners `z₀, z₀+a, z₀+a+c, z₀+c` (both sides free). -/
noncomputable def parContourGen (g : ℂ → ℂ) (z₀ a c : ℂ) : ℂ :=
  a * (∫ t : ℝ in (0)..1, g (z₀ + (t : ℂ) * a))
    + c * (∫ t : ℝ in (0)..1, g (z₀ + a + (t : ℂ) * c))
    - a * (∫ t : ℝ in (0)..1, g (z₀ + c + (t : ℂ) * a))
    - c * (∫ t : ℝ in (0)..1, g (z₀ + (t : ℂ) * c))

/-- Cauchy for `parContourGen` given a primitive on a convex set containing the corners. -/
theorem parContourGen_eq_zero_of_exactOn (G g : ℂ → ℂ) (U : Set ℂ) (hU : Convex ℝ U)
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U) (z₀ a c : ℂ)
    (h0 : z₀ ∈ U) (ha : z₀ + a ∈ U) (hac : z₀ + a + c ∈ U) (hc : z₀ + c ∈ U) :
    parContourGen g z₀ a c = 0 := by
  have hseg : ∀ p v : ℂ, p ∈ U → p + v ∈ U →
      v * (∫ t : ℝ in (0)..1, g (p + (t : ℂ) * v)) = G (p + v) - G p := by
    intro p v hp hpv
    rw [← intervalIntegral.integral_const_mul]
    have hmaps : Set.MapsTo (fun t : ℝ => p + (t : ℂ) * v) (Set.uIcc 0 1) U := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have hcv := hU hp hpv (sub_nonneg.mpr ht.2) ht.1 (by ring)
      rw [Complex.real_smul, Complex.real_smul] at hcv
      convert hcv using 1; push_cast; ring
    have key : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 →
        HasDerivAt (fun s : ℝ => G (p + (s : ℂ) * v)) (v * g (p + (t : ℂ) * v)) t := by
      intro t ht
      have hpath : HasDerivAt (fun s : ℝ => p + (s : ℂ) * v) v t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add p
      have := (hG (p + (t : ℂ) * v) (hmaps ht)).comp_of_eq t hpath rfl
      rw [mul_comm]; exact this
    have hcont : ContinuousOn (fun t : ℝ => v * g (p + (t : ℂ) * v)) (Set.uIcc (0:ℝ) 1) := by
      apply ContinuousOn.mul continuousOn_const
      exact hg.comp (by fun_prop) hmaps
    rw [integral_eq_sub_of_hasDerivAt key hcont.intervalIntegrable]; simp
  unfold parContourGen
  rw [hseg z₀ a h0 ha, hseg z₀ c h0 hc, hseg (z₀+a) c ha hac,
    hseg (z₀+c) a hc (by rw [show z₀+c+a = z₀+a+c by ring]; exact hac),
    show z₀ + c + a = z₀ + a + c by ring]
  ring

/-- Disk base case for `parContourGen`. -/
theorem parContourGen_eq_zero_of_ball (g : ℂ → ℂ) (z₀ a c cen : ℂ) (R : ℝ)
    (hg : DifferentiableOn ℂ g (Metric.ball cen R))
    (h0 : z₀ ∈ Metric.ball cen R) (ha : z₀ + a ∈ Metric.ball cen R)
    (hac : z₀ + a + c ∈ Metric.ball cen R) (hc : z₀ + c ∈ Metric.ball cen R) :
    parContourGen g z₀ a c = 0 := by
  obtain ⟨G, hG⟩ := DifferentiableOn.isExactOn_ball hg
  exact parContourGen_eq_zero_of_exactOn G g (Metric.ball cen R) (convex_ball cen R)
    hG hg.continuousOn z₀ a c h0 ha hac hc

/-- Subdivide `parContourGen` in the `c`-direction. -/
theorem parContourGen_split_c (g : ℂ → ℂ) (z₀ a c : ℂ)
    (hIr : IntervalIntegrable (fun t : ℝ => g (z₀ + a + (t : ℂ) * c)) MeasureTheory.volume 0 1)
    (hIl : IntervalIntegrable (fun t : ℝ => g (z₀ + (t : ℂ) * c)) MeasureTheory.volume 0 1) :
    parContourGen g z₀ a c = parContourGen g z₀ a (c/2) + parContourGen g (z₀ + c/2) a (c/2) := by
  unfold parContourGen
  rw [slant_split g (z₀ + a) c hIr, slant_split g z₀ c hIl]
  rw [show (∫ t in (0:ℝ)..1, g (z₀ + c/2 + c/2 + (t : ℂ)*a))
        = ∫ t in (0:ℝ)..1, g (z₀ + c + (t : ℂ)*a) from
      intervalIntegral.integral_congr (fun t _ => by congr 2; ring),
    show (∫ t in (0:ℝ)..1, g (z₀ + c/2 + a + (t : ℂ)*(c/2)))
        = ∫ t in (0:ℝ)..1, g (z₀ + a + c/2 + (t : ℂ)*(c/2)) from
      intervalIntegral.integral_congr (fun t _ => by congr 2; ring)]
  ring

/-- Subdivide `parContourGen` in the `a`-direction. -/
theorem parContourGen_split_a (g : ℂ → ℂ) (z₀ a c : ℂ)
    (hIb : IntervalIntegrable (fun t : ℝ => g (z₀ + (t : ℂ) * a)) MeasureTheory.volume 0 1)
    (hIt : IntervalIntegrable (fun t : ℝ => g (z₀ + c + (t : ℂ) * a)) MeasureTheory.volume 0 1) :
    parContourGen g z₀ a c = parContourGen g z₀ (a/2) c + parContourGen g (z₀ + a/2) (a/2) c := by
  unfold parContourGen
  rw [slant_split g z₀ a hIb, slant_split g (z₀ + c) a hIt]
  rw [show (∫ t in (0:ℝ)..1, g (z₀ + a/2 + a/2 + (t : ℂ)*c))
        = ∫ t in (0:ℝ)..1, g (z₀ + a + (t : ℂ)*c) from
      intervalIntegral.integral_congr (fun t _ => by congr 2; ring),
    show (∫ t in (0:ℝ)..1, g (z₀ + a/2 + c + (t : ℂ)*(a/2)))
        = ∫ t in (0:ℝ)..1, g (z₀ + c + a/2 + (t : ℂ)*(a/2)) from
      intervalIntegral.integral_congr (fun t _ => by congr 2; ring)]
  ring

/-- **Full parallelogram Cauchy (Cauchy–Goursat for a slanted cell).**  If `g` is holomorphic on
an open set containing the closed cell, its contour integral vanishes — proved by quadrisecting the cell
(`parContourGen_split_a`/`_c`) until every sub-cell is small enough (via a compactness/Lebesgue-number
step) to fit in a zero-free disk (`parContourGen_eq_zero_of_ball`).  This is the Cauchy theorem for
slanted parallelograms that Mathlib provides only for rectangles/disks/annuli. -/
theorem seg_integrable_of_mem (g : ℂ → ℂ) (U : Set ℂ) (hg : ContinuousOn g U) (p v : ℂ)
    (hmem : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → p + (t:ℂ) * v ∈ U) :
    IntervalIntegrable (fun t : ℝ => g (p + (t:ℂ) * v)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  exact hg.comp (by fun_prop) (fun t ht => hmem t ht)

theorem parContourGen_eq_zero_of_holo (g : ℂ → ℂ) (U : Set ℂ) (hUo : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (z₀ a c : ℂ)
    (hcell : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      z₀ + (s:ℂ) * a + (t:ℂ) * c ∈ U) :
    parContourGen g z₀ a c = 0 := by
  set K : Set ℂ :=
    (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * a + (p.2 : ℂ) * c) '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) with hKdef
  have hKcompact : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKU : K ⊆ U := by rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩; exact hcell s t hs ht
  obtain ⟨ε, hε, hthick⟩ := hKcompact.exists_thickening_subset_open hUo hKU
  have hgc : ContinuousOn g U := hg.continuousOn
  suffices H : ∀ n : ℕ, ∀ z₀' a' c' : ℂ,
      (∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → z₀' + (s:ℂ) * a' + (t:ℂ) * c' ∈ K) →
      ‖a'‖ + ‖c'‖ < ε * 2 ^ n → parContourGen g z₀' a' c' = 0 by
    obtain ⟨n, hn⟩ := exists_nat_gt ((‖a‖ + ‖c‖) / ε)
    refine H n z₀ a c (fun s t hs ht => ⟨(s, t), ⟨hs, ht⟩, rfl⟩) ?_
    rw [div_lt_iff₀ hε] at hn
    have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    calc ‖a‖ + ‖c‖ < (n : ℝ) * ε := hn
      _ ≤ 2 ^ n * ε := by apply mul_le_mul_of_nonneg_right h2n hε.le
      _ = ε * 2 ^ n := by ring
  intro n
  induction n with
  | zero =>
    intro z₀' a' c' hsub hsmall
    simp only [pow_zero, mul_one] at hsmall
    have hz₀'K : z₀' ∈ K := by
      have := hsub 0 0 ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩; simpa using this
    have hgb : DifferentiableOn ℂ g (Metric.ball z₀' ε) :=
      hg.mono ((Metric.ball_subset_thickening hz₀'K ε).trans hthick)
    refine parContourGen_eq_zero_of_ball g z₀' a' c' z₀' ε hgb (Metric.mem_ball_self hε) ?_ ?_ ?_
    · rw [Metric.mem_ball, Complex.dist_eq, show (z₀' + a') - z₀' = a' by ring]
      exact lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg c')) hsmall
    · rw [Metric.mem_ball, Complex.dist_eq, show (z₀' + a' + c') - z₀' = a' + c' by ring]
      exact lt_of_le_of_lt (norm_add_le a' c') hsmall
    · rw [Metric.mem_ball, Complex.dist_eq, show (z₀' + c') - z₀' = c' by ring]
      exact lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg a')) hsmall
  | succ n ih =>
    intro z₀' a' c' hsub hsmall
    have hle : (0:ℝ) ≤ 1 := by norm_num
    have hhalf : ‖a' / 2‖ + ‖c' / 2‖ < ε * 2 ^ n := by
      have he : ‖a' / 2‖ + ‖c' / 2‖ = (‖a'‖ + ‖c'‖) / 2 := by
        rw [norm_div, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]; ring
      rw [he, pow_succ] at *; linarith
    -- membership of a "vertical" side (fixed s0) as a segment in U
    have vmem : ∀ (s0 : ℝ), s0 ∈ Set.Icc (0:ℝ) 1 → ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 →
        z₀' + (s0:ℂ) * a' + (t:ℂ) * c' ∈ U := by
      intro s0 hs0 t ht; rw [Set.uIcc_of_le hle] at ht; exact hKU (hsub s0 t hs0 ht)
    have hmem : ∀ (t0 : ℝ), t0 ∈ Set.Icc (0:ℝ) 1 → ∀ s : ℝ, s ∈ Set.uIcc (0:ℝ) 1 →
        z₀' + (s:ℂ) * a' + (t0:ℂ) * c' ∈ U := by
      intro t0 ht0 s hs; rw [Set.uIcc_of_le hle] at hs; exact hKU (hsub s t0 hs ht0)
    -- integrabilities
    have hIl : IntervalIntegrable (fun t : ℝ => g (z₀' + (t:ℂ) * c')) MeasureTheory.volume 0 1 :=
      seg_integrable_of_mem g U hgc z₀' c' (fun t ht => by
        simpa using vmem 0 ⟨le_refl 0, zero_le_one⟩ t ht)
    have hIr : IntervalIntegrable (fun t : ℝ => g (z₀' + a' + (t:ℂ) * c')) MeasureTheory.volume 0 1 :=
      seg_integrable_of_mem g U hgc (z₀' + a') c' (fun t ht => by
        have := vmem 1 ⟨zero_le_one, le_refl 1⟩ t ht; simpa using this)
    have hIb1 : IntervalIntegrable (fun t : ℝ => g (z₀' + (t:ℂ) * a')) MeasureTheory.volume 0 1 :=
      seg_integrable_of_mem g U hgc z₀' a' (fun s hs => by
        simpa using hmem 0 ⟨le_refl 0, zero_le_one⟩ s hs)
    have hIt1 : IntervalIntegrable (fun t : ℝ => g (z₀' + c'/2 + (t:ℂ) * a')) MeasureTheory.volume 0 1 :=
      seg_integrable_of_mem g U hgc (z₀' + c'/2) a' (fun s hs => by
        have := hmem (1/2) ⟨by norm_num, by norm_num⟩ s hs
        rw [show z₀' + (s:ℂ)*a' + ((1/2:ℝ):ℂ)*c' = (z₀' + c'/2) + (s:ℂ)*a' by push_cast; ring] at this
        exact this)
    have hIt2 : IntervalIntegrable (fun t : ℝ => g (z₀' + c'/2 + c'/2 + (t:ℂ) * a')) MeasureTheory.volume 0 1 :=
      seg_integrable_of_mem g U hgc (z₀' + c'/2 + c'/2) a' (fun s hs => by
        have := hmem 1 ⟨zero_le_one, le_refl 1⟩ s hs
        rw [show z₀' + (s:ℂ)*a' + ((1:ℝ):ℂ)*c' = (z₀' + c'/2 + c'/2) + (s:ℂ)*a' by push_cast; ring] at this
        exact this)
    -- quarter sub-cell memberships
    have hQ1 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
        z₀' + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) ∈ K := by
      intro s t hs ht
      rw [show z₀' + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) = z₀' + ((s/2:ℝ):ℂ)*a' + ((t/2:ℝ):ℂ)*c' by push_cast; ring]
      exact hsub (s/2) (t/2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hQ2 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
        (z₀' + a'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) ∈ K := by
      intro s t hs ht
      rw [show (z₀' + a'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) = z₀' + (((1+s)/2:ℝ):ℂ)*a' + ((t/2:ℝ):ℂ)*c' by push_cast; ring]
      exact hsub ((1+s)/2) (t/2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hQ3 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
        (z₀' + c'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) ∈ K := by
      intro s t hs ht
      rw [show (z₀' + c'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) = z₀' + ((s/2:ℝ):ℂ)*a' + (((1+t)/2:ℝ):ℂ)*c' by push_cast; ring]
      exact hsub (s/2) ((1+t)/2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hQ4 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
        (z₀' + c'/2 + a'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) ∈ K := by
      intro s t hs ht
      rw [show (z₀' + c'/2 + a'/2) + (s:ℂ)*(a'/2) + (t:ℂ)*(c'/2) = z₀' + (((1+s)/2:ℝ):ℂ)*a' + (((1+t)/2:ℝ):ℂ)*c' by push_cast; ring]
      exact hsub ((1+s)/2) ((1+t)/2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [parContourGen_split_c g z₀' a' c' hIr hIl,
      parContourGen_split_a g z₀' a' (c'/2) hIb1 hIt1,
      parContourGen_split_a g (z₀' + c'/2) a' (c'/2) hIt1 hIt2,
      ih z₀' (a'/2) (c'/2) hQ1 hhalf, ih (z₀' + a'/2) (a'/2) (c'/2) hQ2 hhalf,
      ih (z₀' + c'/2) (a'/2) (c'/2) hQ3 hhalf, ih (z₀' + c'/2 + a'/2) (a'/2) (c'/2) hQ4 hhalf]
    ring

/-- `parContourIntegral` is the `a=1` case of `parContourGen`. -/
theorem parContourIntegral_eq_gen (g : ℂ → ℂ) (z₀ c : ℂ) :
    parContourIntegral g z₀ c = parContourGen g z₀ 1 c := by
  unfold parContourIntegral parContourGen
  rw [one_mul, one_mul,
    show (∫ t : ℝ in (0)..1, g (z₀ + (t : ℂ) * 1)) = ∫ t : ℝ in (0)..1, g (z₀ + (t : ℂ)) from
      intervalIntegral.integral_congr (fun t _ => by rw [mul_one]),
    show (∫ t : ℝ in (0)..1, g (z₀ + c + (t : ℂ) * 1)) = ∫ t : ℝ in (0)..1, g (z₀ + c + (t : ℂ)) from
      intervalIntegral.integral_congr (fun t _ => by rw [mul_one])]

/-- **Full parallelogram Cauchy for `parContourIntegral`.**  If `g` is holomorphic on an open set
containing the closed fundamental cell (sides `1` and `c`), the contour integral vanishes. -/
theorem parContourIntegral_eq_zero_of_holo (g : ℂ → ℂ) (U : Set ℂ) (hUo : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (z₀ c : ℂ)
    (hcell : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      z₀ + (s : ℂ) + (t : ℂ) * c ∈ U) :
    parContourIntegral g z₀ c = 0 := by
  rw [parContourIntegral_eq_gen]
  refine parContourGen_eq_zero_of_holo g U hUo hg z₀ 1 c (fun s t hs ht => ?_)
  simpa using hcell s t hs ht

/-! ### Log-derivative principal part (toward the argument principle)

The residue-theorem input for the *argument principle*: near a zero `ζ` of order `m` of an analytic
`f` (factored `f =ᶠ (·−ζ)^m • u` with `u` analytic, `u ζ ≠ 0` — Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast`), the logarithmic derivative has a **simple pole with residue
`m`**: `logDeriv f = m/(·−ζ) + logDeriv u` on a punctured neighbourhood, with `logDeriv u` analytic.
Combined with the winding number and localized Cauchy this yields `∮_∂P θ'/θ = m·2πi`, and against the
log-derivative periodicity (`∮ = 2πi`) forces the degree-one theta section to have a **simple zero**
(`m = 1`) — the order fact F1's ratio-holomorphy step needs. -/
theorem logDeriv_principal_part {f u : ℂ → ℂ} {ζ : ℂ} {m : ℕ}
    (hu : AnalyticAt ℂ u ζ) (hune : u ζ ≠ 0)
    (hfac : f =ᶠ[𝓝 ζ] fun z => (z - ζ) ^ m • u z) :
    ∀ᶠ z in 𝓝[≠] ζ, logDeriv f z = (m : ℂ) / (z - ζ) + logDeriv u z := by
  have hderiv : deriv f =ᶠ[𝓝 ζ] deriv (fun z => (z - ζ) ^ m • u z) := hfac.deriv
  have hlog : logDeriv f =ᶠ[𝓝 ζ] logDeriv (fun z => (z - ζ) ^ m • u z) := by
    filter_upwards [hfac, hderiv] with z hz hdz
    simp only [logDeriv_apply, hz, hdz]
  have hune' : ∀ᶠ z in 𝓝 ζ, u z ≠ 0 := hu.continuousAt.eventually_ne hune
  have hduev : ∀ᶠ z in 𝓝 ζ, DifferentiableAt ℂ u z :=
    hu.eventually_analyticAt.mono (fun z hz => hz.differentiableAt)
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    hune'.filter_mono nhdsWithin_le_nhds, hduev.filter_mono nhdsWithin_le_nhds]
    with z hzlog hzne hzune hzdu
  rw [hzlog]
  have hznez : z - ζ ≠ 0 := sub_ne_zero.mpr hzne
  have hpowne : (z - ζ) ^ m ≠ 0 := pow_ne_zero _ hznez
  have hdsub : DifferentiableAt ℂ (fun z => z - ζ) z := by fun_prop
  have hdpow : DifferentiableAt ℂ (fun z => (z - ζ) ^ m) z := by fun_prop
  rw [show (fun z => (z - ζ) ^ m • u z) = fun z => (z - ζ) ^ m * u z from by
      funext w; rw [smul_eq_mul],
    logDeriv_mul z hpowne hzune hdpow hzdu, logDeriv_fun_pow hdsub m]
  congr 1
  rw [logDeriv_apply, show deriv (fun z => z - ζ) z = 1 by simp, mul_one_div]

/-- **Removable extension of `θ'/θ − m/(·−ζ)` at the zero `ζ`.**  Since this equals the analytic
`logDeriv u` on a punctured neighbourhood (`logDeriv_principal_part`), patching its value at `ζ` to
`logDeriv u ζ` makes it differentiable at `ζ` — the simple pole cancels.  Together with holomorphy off
the zeros this gives the holomorphic `g` whose contour integral (`= 0` by the parallelogram Cauchy)
completes `∮ θ'/θ = m·2πi`. -/
theorem differentiableAt_logDeriv_sub_extend {θ u : ℂ → ℂ} {ζ : ℂ} {m : ℕ}
    (hu : AnalyticAt ℂ u ζ) (hune : u ζ ≠ 0)
    (hfac : θ =ᶠ[𝓝 ζ] fun z => (z - ζ) ^ m • u z) :
    DifferentiableAt ℂ
      (Function.update (fun z => logDeriv θ z - (m : ℂ) / (z - ζ)) ζ (logDeriv u ζ)) ζ := by
  have hpp := logDeriv_principal_part hu hune hfac
  have h₁ : (Function.update (fun z => logDeriv θ z - (m : ℂ) / (z - ζ)) ζ (logDeriv u ζ))
      =ᶠ[𝓝[≠] ζ] logDeriv u := by
    filter_upwards [hpp, self_mem_nhdsWithin] with z hz hzne
    rw [Function.update_of_ne (Set.mem_compl_singleton_iff.mp hzne), hz]; ring
  have h₂ : (Function.update (fun z => logDeriv θ z - (m : ℂ) / (z - ζ)) ζ (logDeriv u ζ)) ζ
      = logDeriv u ζ :=
    Function.update_self ζ (logDeriv u ζ) (fun z => logDeriv θ z - (m : ℂ) / (z - ζ))
  have hev := eventuallyEq_nhds_of_eventuallyEq_nhdsNE h₁ h₂
  have hdlu : DifferentiableAt ℂ (logDeriv u) ζ := by
    show DifferentiableAt ℂ (fun z => deriv u z / u z) ζ
    exact (hu.deriv.differentiableAt).div hu.differentiableAt hune
  exact hev.differentiableAt_iff.mpr hdlu

/-- **Differentiability of the extended `θ'/θ − m/(·−ζ)` away from the zero `ζ`.**  At a point where
`θ` is analytic and non-vanishing (and `≠ ζ`), the update is inert and the function is a difference of
`logDeriv θ` (holomorphic where `θ ≠ 0`) and `m/(·−ζ)` (holomorphic away from `ζ`). -/
theorem differentiableAt_logDeriv_sub_away {θ : ℂ → ℂ} {ζ z c : ℂ} {m : ℕ}
    (hθ : AnalyticAt ℂ θ z) (hθ0 : θ z ≠ 0) (hzζ : z ≠ ζ) :
    DifferentiableAt ℂ (Function.update (fun w => logDeriv θ w - (m : ℂ) / (w - ζ)) ζ c) z := by
  have hev : (Function.update (fun w => logDeriv θ w - (m : ℂ) / (w - ζ)) ζ c)
      =ᶠ[𝓝 z] (fun w => logDeriv θ w - (m : ℂ) / (w - ζ)) := by
    filter_upwards [isOpen_ne.mem_nhds hzζ] with w hw
    exact Function.update_of_ne hw c (fun w => logDeriv θ w - (m : ℂ) / (w - ζ))
  rw [hev.differentiableAt_iff]
  have h1 : DifferentiableAt ℂ (logDeriv θ) z := by
    show DifferentiableAt ℂ (fun w => deriv θ w / θ w) z
    exact (hθ.deriv.differentiableAt).div hθ.differentiableAt hθ0
  have h2 : DifferentiableAt ℂ (fun w => (m : ℂ) / (w - ζ)) z :=
    (differentiableAt_const (m : ℂ)).div (by fun_prop) (sub_ne_zero.mpr hzζ)
  exact h1.sub h2

/-- **Periodicity half of the argument principle.**  A function with the logarithmic-derivative
quasi-periodicity of a level-`Ω` theta — period `1` (`f(z+1)=f(z)`) and the `−2πi` jump under
`z ↦ z+Ω` (`f(z+Ω)=f(z)−2πi`, which holds for `θ'/θ` off the zeros) — has contour integral `2πi`
around the fundamental parallelogram: the period-`1` sides cancel and the top/bottom differ by
`−2πi·(length 1) = −2πi`.  Against the residue value `m·2πi` this forces the theta's zero order `m=1`. -/
theorem parContourIntegral_logDeriv_eq (f : ℂ → ℂ) (z₀ Ω : ℂ)
    (hper1 : ∀ t : ℝ, f (z₀ + 1 + (t : ℂ) * Ω) = f (z₀ + (t : ℂ) * Ω))
    (hjump : ∀ t : ℝ, f (z₀ + Ω + (t : ℂ)) = f (z₀ + (t : ℂ)) - 2 * (Real.pi : ℂ) * I)
    (hint : IntervalIntegrable (fun t : ℝ => f (z₀ + (t : ℂ))) MeasureTheory.volume 0 1) :
    parContourIntegral f z₀ Ω = 2 * (Real.pi : ℂ) * I := by
  unfold parContourIntegral
  have hright : (∫ t in (0 : ℝ)..1, f (z₀ + 1 + (t : ℂ) * Ω))
      = ∫ t in (0 : ℝ)..1, f (z₀ + (t : ℂ) * Ω) :=
    intervalIntegral.integral_congr (fun t _ => hper1 t)
  have htop : (∫ t in (0 : ℝ)..1, f (z₀ + Ω + (t : ℂ)))
      = (∫ t in (0 : ℝ)..1, f (z₀ + (t : ℂ))) - 2 * (Real.pi : ℂ) * I := by
    rw [show (∫ t in (0 : ℝ)..1, f (z₀ + Ω + (t : ℂ)))
        = ∫ t in (0 : ℝ)..1, (f (z₀ + (t : ℂ)) - 2 * (Real.pi : ℂ) * I) from
      intervalIntegral.integral_congr (fun t _ => hjump t),
      intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp
  rw [hright, htop]
  ring

end LyubarskiiNes.FrobeniusDeterminant.ResidueTheorem
