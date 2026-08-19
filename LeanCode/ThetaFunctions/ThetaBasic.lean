import LeanCode.ComplexAnalysis.DivisionByDivisor

namespace LyubarskiiNes.ThetaFunctions

/-- The paper's theta function, in Mathlib coordinates. -/
noncomputable def theta (τ z : ℂ) : ℂ := jacobiTheta₂ z τ

/-- The theta function is periodic under translation by one. -/
theorem theta_add_one_eq (τ z : ℂ) : theta τ (z + 1) = theta τ z := by
  simpa [theta] using jacobiTheta₂_add_left z τ

/-- The theta function is quasi-periodic under translation by `τ`. -/
theorem theta_add_tau_eq (τ z : ℂ) :
    theta τ (z + τ) = Complex.exp (-↑Real.pi * Complex.I * (τ + 2 * z)) * theta τ z := by
  simpa [theta] using jacobiTheta₂_add_left' z τ

/-- The theta function is even. -/
theorem theta_neg_eq (τ z : ℂ) : theta τ (-z) = theta τ z := by
  simp [theta]

/-- The theta function is complex differentiable in `z` when `τ` lies in the upper half-plane. -/
theorem differentiableAt_theta (τ z : ℂ) (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun w => theta τ w) z := by
  simpa [theta] using differentiableAt_jacobiTheta₂_fst z hτ

/-- Derivative wrapper for theta in the first variable. -/
theorem hasDerivAt_theta (τ z : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w => theta τ w) (jacobiTheta₂' z τ) z := by
  simpa [theta] using hasDerivAt_jacobiTheta₂_fst z hτ

end LyubarskiiNes.ThetaFunctions
