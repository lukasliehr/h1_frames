import LeanCode.Definitions

namespace Zak

open scoped BigOperators

/-- The oscillatory phase in the Zak-transform series. -/
noncomputable def zakPhase (ρ : ℝ) (k : ℤ) (ω : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ))

/-- The Zak transform with lattice parameter `ρ`, defined by its formal `tsum`.

The theorem `zakTransform_basic` below packages the convergence-from-summability
and quasi-periodicity facts now available for this concrete definition. -/
noncomputable def zakTransform (ρ : ℝ) (f : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x ω => ∑' k : ℤ,
    f (x - ρ * (k : ℝ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ))

@[simp]
theorem zakTransform_apply (ρ : ℝ) (f : ℝ → ℂ) (x ω : ℝ) :
    zakTransform ρ f x ω = ∑' k : ℤ,
      f (x - ρ * (k : ℝ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ)) :=
  rfl

/-- The same defining series written using the named phase factor. -/
theorem zakTransform_eq_tsum_zakPhase (ρ : ℝ) (f : ℝ → ℂ) (x ω : ℝ) :
    zakTransform ρ f x ω = ∑' k : ℤ, f (x - ρ * (k : ℝ)) * zakPhase ρ k ω := by
  simp [zakTransform, zakPhase]

/-- The Zak phase has unit norm. -/
theorem norm_zakPhase (ρ : ℝ) (k : ℤ) (ω : ℝ) :
    ‖zakPhase ρ k ω‖ = 1 := by
  unfold zakPhase
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ) =
        ((2 * Real.pi * ρ * (k : ℝ) * ω : ℝ) : ℂ) * Complex.I := by
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The absolute value of a Zak-series term is just the absolute value of the sample. -/
theorem norm_zakTransform_term (ρ : ℝ) (f : ℝ → ℂ) (x ω : ℝ) (k : ℤ) :
    ‖f (x - ρ * (k : ℝ)) * zakPhase ρ k ω‖ = ‖f (x - ρ * (k : ℝ))‖ := by
  rw [norm_mul, norm_zakPhase, mul_one]

/-- Norm-summability of the lattice samples implies summability of the Zak-series terms. -/
theorem summable_zakTransform_terms_of_norm_summable
    {ρ : ℝ} {f : ℝ → ℂ} {x ω : ℝ}
    (hf : Summable fun k : ℤ => ‖f (x - ρ * (k : ℝ))‖) :
    Summable fun k : ℤ => f (x - ρ * (k : ℝ)) * zakPhase ρ k ω := by
  refine Summable.of_norm ?_
  exact hf.congr fun k => (norm_zakTransform_term ρ f x ω k).symm

/-- Frequency quasi-periodicity of the Zak transform. This part is termwise and
does not require a separate summability hypothesis. -/
theorem zakTransform_freq_period {ρ : ℝ} (hρ : ρ ≠ 0) (f : ℝ → ℂ) (x ω : ℝ) :
    zakTransform ρ f x (ω + ρ⁻¹) = zakTransform ρ f x ω := by
  unfold zakTransform
  refine tsum_congr ?_
  intro k
  congr 1
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * ((ω + ρ⁻¹ : ℝ) : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ)) +
          ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    norm_num [Complex.ofReal_add, Complex.ofReal_inv]
    field_simp [hρc]
  rw [hphase, Complex.exp_add]
  rw [show Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 by
    exact Complex.exp_int_mul_two_pi_mul_I k]
  simp

/-- Spatial quasi-periodicity of the Zak transform, by reindexing the defining
series. -/
theorem zakTransform_add_period (ρ : ℝ) (f : ℝ → ℂ) (x ω : ℝ) :
    zakTransform ρ f (x + ρ) ω =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (ω : ℂ)) *
        zakTransform ρ f x ω := by
  unfold zakTransform
  let C : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (ω : ℂ))
  let term : ℤ → ℂ := fun k =>
    f (x - ρ * (k : ℝ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ))
  calc
    (∑' k : ℤ,
      f (x + ρ - ρ * (k : ℝ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ))) =
        ∑' j : ℤ,
          f (x + ρ - ρ * ((j + 1 : ℤ) : ℝ)) *
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * ((j + 1 : ℤ) : ℂ) *
                (ω : ℂ)) := by
      exact ((Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ =>
        f (x + ρ - ρ * (k : ℝ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) * (ω : ℂ)))).symm
    _ = ∑' j : ℤ, C * term j := by
      refine tsum_congr ?_
      intro j
      have hx : x + ρ - ρ * ((j + 1 : ℤ) : ℝ) = x - ρ * (j : ℝ) := by
        norm_num [Int.cast_add]
        ring
      have hphase :
          2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * ((j + 1 : ℤ) : ℂ) *
              (ω : ℂ) =
            (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (j : ℂ) * (ω : ℂ)) +
              (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (ω : ℂ)) := by
        norm_num [Int.cast_add]
        ring
      unfold term C
      rw [hx, hphase, Complex.exp_add]
      ring
    _ = C * ∑' j : ℤ, term j := by
      exact (tsum_mul_left (f := term) (a := C))
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (ω : ℂ)) *
        (∑' k : ℤ,
          f (x - ρ * (k : ℝ)) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ρ : ℂ) * (k : ℂ) *
              (ω : ℂ))) := by
      rfl

end Zak
