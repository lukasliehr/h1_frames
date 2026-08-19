import LeanCode.RationalDensity.RationalPositive.ComponentEnergy

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- The basic rational-Zak scale identity `η p = γ`. -/
lemma rationalZakEta_mul_p_eq_gamma {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    rationalZakEta α p q * (p : ℝ) = rationalZakGamma α q := by
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp_nat)
  unfold rationalZakEta
  field_simp [hp]

/-- The gamma-fiber `X_x` from `Part7_student.tex`, expressed through the
already constructed shifted honest fiber `v_x` by the student-corrected finite
Fourier relation `X = p⁻¹ D(ξ)^* v`. -/
noncomputable def rationalPositiveGammaFiberField
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : Fin p → ℂ :=
  ((p : ℂ)⁻¹) •
    ((rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ
      rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z)

/-- A.e. strong measurability of the student-corrected gamma fiber `X_x`. -/
theorem rationalPositiveGammaFiberField_aestronglyMeasurable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z)
      (volume : Measure (ℝ × ℝ)) := by
  have hD_cont : Continuous (fun z : ℝ × ℝ =>
      Matrix.conjTranspose (rationalPositiveFourierRowChange α p q z)) := by
    simpa using
      continuous_conjTranspose_matrix_field
        (P := rationalPositiveFourierRowChange α p q)
        (continuous_rationalPositiveFourierRowChange α p q)
  have hD_comp :
      ∀ i j, AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          Matrix.conjTranspose (rationalPositiveFourierRowChange α p q z) i j)
        (volume : Measure (ℝ × ℝ)) := by
    intro i j
    exact ((continuous_apply j).comp
      ((continuous_apply i).comp hD_cont)).aestronglyMeasurable
  have hv_comp :
      ∀ j, AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z j)
        (volume : Measure (ℝ × ℝ)) :=
    Zak.vector_components_aestronglyMeasurable
      (fun z : ℝ × ℝ =>
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z)
      (rationalPositiveFiberField_aestronglyMeasurable
        hα hβ hpq_coprime hgap hαβ x)
  have hmul := Zak.matrix_mulVec_aestronglyMeasurable_of_components
    (M := fun z : ℝ × ℝ =>
      Matrix.conjTranspose (rationalPositiveFourierRowChange α p q z))
    (v := fun z : ℝ × ℝ =>
      rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z)
    hD_comp hv_comp
  refine (hmul.const_smul ((p : ℂ)⁻¹)).congr ?_
  exact Filter.Eventually.of_forall fun z => by
    simp [rationalPositiveGammaFiberField]

/-- Student-corrected gamma-fiber matrix energy with prefactor `η γ`. -/
noncomputable def rationalPositiveGammaMatrixEnergy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : ℝ :=
  rationalZakEta α p q * rationalZakGamma α q *
    ‖rationalZakMatrix α p q z *ᵥ
      rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2

end LyubarskiiNes.RationalDensity
