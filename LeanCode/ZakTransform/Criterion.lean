import LeanCode.ZakTransform.Refinement

open scoped Matrix ComplexOrder
open MeasureTheory

namespace Zak

/-- If two nonnegative-energy functions satisfy uniform pointwise bounds a.e.,
then their integrals satisfy the same bounds.  This is the scalar integration
step used by the rational Zak coefficient-transfer argument. -/
theorem integral_bounds_of_ae_pointwise_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {lower upper : ℝ} {u v : Ω → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hlower : ∀ᵐ t ∂μ, lower * u t ≤ v t)
    (hupper : ∀ᵐ t ∂μ, v t ≤ upper * u t) :
    lower * (∫ t, u t ∂μ) ≤ ∫ t, v t ∂μ ∧
      ∫ t, v t ∂μ ≤ upper * (∫ t, u t ∂μ) := by
  constructor
  · rw [← integral_const_mul]
    exact integral_mono_ae (hu.const_mul lower) hv hlower
  · rw [← integral_const_mul]
    exact integral_mono_ae hv (hu.const_mul upper) hupper

/-- Abstract coefficient-transfer package: if a coefficient energy and the
ambient norm energy are represented by two integral energies, and those
integral energies satisfy uniform a.e. pointwise bounds, then the coefficient
energy satisfies global frame-style bounds.

The final rational-Zak step should instantiate this with the concrete
rectangle fiber energy and the rational Zak matrix energy. -/
theorem coefficient_bounds_of_ae_integral_transfer
    {X Ω : Type*} [Norm X] [MeasurableSpace Ω] (μ : Measure Ω)
    {lower upper : ℝ} {coeffEnergy : X → ℝ}
    {fiberEnergy matrixEnergy : X → Ω → ℝ}
    (hlower_pos : 0 < lower) (hle : lower ≤ upper)
    (hfiber_int : ∀ x, Integrable (fiberEnergy x) μ)
    (hmatrix_int : ∀ x, Integrable (matrixEnergy x) μ)
    (hnorm : ∀ x, ∫ t, fiberEnergy x t ∂μ = ‖x‖ ^ 2)
    (hcoeff : ∀ x, coeffEnergy x = ∫ t, matrixEnergy x t ∂μ)
    (hpt_lower : ∀ x, ∀ᵐ t ∂μ, lower * fiberEnergy x t ≤ matrixEnergy x t)
    (hpt_upper : ∀ x, ∀ᵐ t ∂μ, matrixEnergy x t ≤ upper * fiberEnergy x t) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : X,
      A * ‖x‖ ^ 2 ≤ coeffEnergy x ∧ coeffEnergy x ≤ B * ‖x‖ ^ 2 := by
  refine ⟨lower, upper, hlower_pos, hle, ?_⟩
  intro x
  have hbounds := integral_bounds_of_ae_pointwise_bounds μ
    (hfiber_int x) (hmatrix_int x) (hpt_lower x) (hpt_upper x)
  constructor
  · calc
      lower * ‖x‖ ^ 2 = lower * (∫ t, fiberEnergy x t ∂μ) := by
        rw [hnorm x]
      _ ≤ ∫ t, matrixEnergy x t ∂μ := hbounds.1
      _ = coeffEnergy x := (hcoeff x).symm
  · calc
      coeffEnergy x = ∫ t, matrixEnergy x t ∂μ := hcoeff x
      _ ≤ upper * (∫ t, fiberEnergy x t ∂μ) := hbounds.2
      _ = upper * ‖x‖ ^ 2 := by
        rw [hnorm x]

end Zak
