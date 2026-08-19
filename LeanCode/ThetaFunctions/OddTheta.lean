import LeanCode.ThetaFunctions.Tp

namespace LyubarskiiNes.ThetaFunctions

/-- Closed-form odd theta section used in the jet-rank argument. -/
noncomputable def oddTheta (τ : ℂ) : ℂ → ℂ :=
  fun z =>
    Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I * z) *
      theta τ (z + (1 + τ) / 2)

@[simp]
theorem oddTheta_apply (τ z : ℂ) :
    oddTheta τ z =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I * z) *
        theta τ (z + (1 + τ) / 2) :=
  rfl

/-- The closed-form odd theta section is antiperiodic under translation by one. -/
theorem oddTheta_add_one_eq (τ z : ℂ) : oddTheta τ (z + 1) = -oddTheta τ z := by
  unfold oddTheta
  rw [show z + 1 + (1 + τ) / 2 = (z + (1 + τ) / 2) + 1 by ring]
  rw [theta_add_one_eq]
  rw [show (Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I * (z + 1) =
      ((Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I * z) +
        (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

end LyubarskiiNes.ThetaFunctions
