import LeanCode.GeneralLattice.GeneralizedCriterion
import LeanCode.GeneralLattice.FrameTransfer

open MeasureTheory
open scoped BigOperators Matrix

namespace LyubarskiiNes.GeneralLattice

open LyubarskiiNes.RationalDensity
open GeneralizedCriterion

private lemma p_pos_of_coprime_gap {p q : ℕ}
    (hpq : Nat.Coprime p q) (hgap : q ≥ p + 2) :
    0 < p := by
  by_contra hp
  have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
  subst p
  have hq1 : q = 1 := (Nat.coprime_zero_left q).mp hpq
  omega

/-- The Euclidean generalized-Zak matrix energy used by the coefficient
identity, as a pointwise function on the rational fundamental rectangle. -/
noncomputable def generalizedMatrixEnergy
    {τ : ℂ} {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq : Nat.Coprime p q) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : ℝ :=
  rationalZakEta α p q * rationalZakGamma α q *
    ∑ t : Fin q,
      ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq hgap hαβ x z) t‖ ^ 2

private theorem generalizedMatrixEnergy_integrable
    {τ : ℂ} (hτ : 0 < τ.im) {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq : Nat.Coprime p q) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (generalizedMatrixEnergy (τ := τ) hα hβ hpq hgap hαβ x)
      (volume : Measure (ℝ × ℝ)) := by
  have hmem := (matrixGammaFiber_memLp hτ hα hβ hpq hgap hαβ x).continuousLinearMap_comp
    (GeneralizedCriterion.toEuclidCLM q)
  have hsum : Integrable (fun z : ℝ × ℝ =>
      ∑ t : Fin q,
        ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    refine (hmem.integrable_norm_pow (p := 2) (by norm_num)).congr ?_
    filter_upwards with z
    exact GeneralizedCriterion.norm_toEuclidCLM_sq q _
  change Integrable (fun z : ℝ × ℝ =>
    (rationalZakEta α p q * rationalZakGamma α q) *
      ∑ t : Fin q,
        ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ))
  exact hsum.const_mul (rationalZakEta α p q * rationalZakGamma α q)

private lemma generalizedMatrixEnergy_pointwise_bounds
    {τ : ℂ} (hτ : 0 < τ.im) {α : ℝ} {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hq : 0 < q) (hα : 0 < α)
    (hpq : Nat.Coprime p q) (hgap : q ≥ p + 2)
    (hαβ : α * (1 : ℝ) = (p : ℝ) / (q : ℝ))
    (hαcanon : α = (p : ℝ) / (q : ℝ)) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ),
        lower *
            (rationalZakEta α p q *
              ∑ r : Fin p,
                ‖rationalPositiveFiberField
                  hα one_pos hpq hgap hαβ x z r‖ ^ 2) ≤
          generalizedMatrixEnergy (τ := τ)
            hα one_pos hpq hgap hαβ x z ∧
        generalizedMatrixEnergy (τ := τ)
            hα one_pos hpq hgap hαβ x z ≤
          upper *
            (rationalZakEta α p q *
              ∑ r : Fin p,
                ‖rationalPositiveFiberField
                  hα one_pos hpq hgap hαβ x z r‖ ^ 2) := by
  rcases generalizedCanonicalZakMatrix_uniform_bounds hp hpq hgap hτ with
    ⟨A, B, hA, hAB, hMlower, hMupper⟩
  rcases rationalPositiveFourierRowChange_conjTranspose_exists_lower_bound α q hp with
    ⟨c, hc, hDlower⟩
  let lower₀ : ℝ := A * c / (p : ℝ) ^ 3
  let upper₀ : ℝ := (q : ℝ) * B
  let lower : ℝ := rationalZakGamma α q * lower₀
  let upper : ℝ := max (rationalZakGamma α q * upper₀) lower
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hlower₀ : 0 < lower₀ := div_pos (mul_pos hA hc) (pow_pos hpR 3)
  have hlower : 0 < lower := mul_pos hγ hlower₀
  refine ⟨lower, upper, hlower, le_max_right _ _, ?_⟩
  intro x z
  let v : Fin p → ℂ := rationalPositiveFiberField hα one_pos hpq hgap hαβ x z
  let D := rationalPositiveFourierRowChange α p q z
  let g : Fin p → ℂ := rationalPositiveGammaFiberField hα one_pos hpq hgap hαβ x z
  let M := generalizedRationalZakMatrix τ α p q z
  let y : Fin q → ℂ := M *ᵥ g
  let CE : ℝ := ∑ r : Fin p, ‖v r‖ ^ 2
  let Esum : ℝ := ∑ t : Fin q, ‖y t‖ ^ 2
  have hMeq : M = generalizedCanonicalZakMatrix τ p q z := by
    have heq := congrFun (generalizedRationalZakMatrix_eq_canonical hp hq τ) z
    simpa [M, hαcanon] using heq
  have hg : g = ((p : ℂ)⁻¹) • (Dᴴ *ᵥ v) := by
    rfl
  have hgnorm : ‖g‖ ^ 2 = ((p : ℝ)⁻¹) ^ 2 * ‖Dᴴ *ᵥ v‖ ^ 2 := by
    rw [hg, norm_smul, mul_pow]
    congr 2
    rw [norm_inv, Complex.norm_natCast]
  have hCE : CE ≤ (p : ℝ) * ‖v‖ ^ 2 := by
    simpa [CE] using finiteVector_sum_norm_sq_le_card_mul_norm_sq v
  have hDlo : c * ‖v‖ ^ 2 ≤ ‖Dᴴ *ᵥ v‖ ^ 2 := by
    simpa [D] using hDlower z v
  have hglo : (c / (p : ℝ) ^ 3) * CE ≤ ‖g‖ ^ 2 := by
    rw [hgnorm]
    calc
      (c / (p : ℝ) ^ 3) * CE
          ≤ (c / (p : ℝ) ^ 3) * ((p : ℝ) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCE (div_nonneg hc.le (pow_pos hpR 3).le)
      _ = ((p : ℝ)⁻¹) ^ 2 * (c * ‖v‖ ^ 2) := by field_simp
      _ ≤ ((p : ℝ)⁻¹) ^ 2 * ‖Dᴴ *ᵥ v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hDlo (sq_nonneg _)
  have hMlo : A * ‖g‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    simpa [M, y, hMeq] using hMlower z g
  have hEsumLo : lower₀ * CE ≤ Esum := by
    have hcore : lower₀ * CE ≤ ‖y‖ ^ 2 := by
      calc
        lower₀ * CE = A * ((c / (p : ℝ) ^ 3) * CE) := by
          dsimp [lower₀]
          ring
        _ ≤ A * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left hglo hA.le
        _ ≤ ‖y‖ ^ 2 := hMlo
    exact le_trans hcore (by
      simpa [Esum] using finiteVector_norm_sq_le_sum_norm_sq y)
  have hDup : ‖Dᴴ *ᵥ v‖ ^ 2 ≤ (p : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    simpa [D] using
      rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_sq_le α p q z v
  have hgup : ‖g‖ ^ 2 ≤ CE := by
    rw [hgnorm]
    calc
      ((p : ℝ)⁻¹) ^ 2 * ‖Dᴴ *ᵥ v‖ ^ 2
          ≤ ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ) ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hDup (sq_nonneg _)
      _ = ‖v‖ ^ 2 := by field_simp
      _ ≤ CE := by simpa [CE] using finiteVector_norm_sq_le_sum_norm_sq v
  have hMup : ‖y‖ ^ 2 ≤ B * ‖g‖ ^ 2 := by
    simpa [M, y, hMeq] using hMupper z g
  have hEsumUp : Esum ≤ upper₀ * CE := by
    calc
      Esum ≤ (q : ℝ) * ‖y‖ ^ 2 := by
        simpa [Esum] using finiteVector_sum_norm_sq_le_card_mul_norm_sq y
      _ ≤ (q : ℝ) * (B * ‖g‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hMup (Nat.cast_nonneg q)
      _ ≤ (q : ℝ) * (B * CE) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgup hB.le) (Nat.cast_nonneg q)
      _ = upper₀ * CE := by simp [upper₀]; ring
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα one_pos hgap hαβ
  have hCE0 : 0 ≤ CE := Finset.sum_nonneg fun r _ ↦ sq_nonneg _
  constructor
  · change lower * (rationalZakEta α p q * CE) ≤
      rationalZakEta α p q * rationalZakGamma α q * Esum
    dsimp [lower]
    calc
      (rationalZakGamma α q * lower₀) * (rationalZakEta α p q * CE) =
          (rationalZakEta α p q * rationalZakGamma α q) * (lower₀ * CE) := by ring
      _ ≤ (rationalZakEta α p q * rationalZakGamma α q) * Esum :=
        mul_le_mul_of_nonneg_left hEsumLo (mul_pos hη hγ).le
  · change rationalZakEta α p q * rationalZakGamma α q * Esum ≤
      upper * (rationalZakEta α p q * CE)
    calc
      rationalZakEta α p q * rationalZakGamma α q * Esum ≤
          rationalZakEta α p q * rationalZakGamma α q * (upper₀ * CE) :=
        mul_le_mul_of_nonneg_left hEsumUp (mul_pos hη hγ).le
      _ = (rationalZakGamma α q * upper₀) *
          (rationalZakEta α p q * CE) := by ring
      _ ≤ upper * (rationalZakEta α p q * CE) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hη.le hCE0)

/-- Positive-direction frame theorem for every generalized first-Hermite
window on the canonical rational lattice. -/
theorem generalized_rational_positive
    {τ : ℂ} (hτ : 0 < τ.im) {p q : ℕ}
    (hpq : Nat.Coprime p q) (hgap : q ≥ p + 2) :
    IsGeneralizedGaborFrame τ hτ ((p : ℝ) / (q : ℝ)) 1 := by
  have hp : 0 < p := p_pos_of_coprime_gap hpq hgap
  have hq : 0 < q := by omega
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let α : ℝ := (p : ℝ) / (q : ℝ)
  have hα : 0 < α := div_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
  have hαβ : α * (1 : ℝ) = (p : ℝ) / (q : ℝ) := by simp [α]
  rcases generalizedMatrixEnergy_pointwise_bounds hτ hp hq hα hpq hgap hαβ
      (by rfl) with
    ⟨lower, upper, hlower, hle, hpoint⟩
  let fiberEnergy : Lp ℂ 2 (volume : Measure ℝ) → ℝ × ℝ → ℝ :=
    fun x z ↦ rationalZakEta α p q *
      ∑ r : Fin p, ‖rationalPositiveFiberField hα one_pos hpq hgap hαβ x z r‖ ^ 2
  let matrixEnergy : Lp ℂ 2 (volume : Measure ℝ) → ℝ × ℝ → ℝ :=
    fun x ↦ generalizedMatrixEnergy (τ := τ) hα one_pos hpq hgap hαβ x
  have hfiber_int : ∀ x, Integrable (fiberEnergy x) (volume : Measure (ℝ × ℝ)) := by
    intro x
    exact (rationalPositiveFiberField_component_energy_integrable
      hα one_pos hpq hgap hαβ x).const_mul (rationalZakEta α p q)
  have hmatrix_int : ∀ x, Integrable (matrixEnergy x) (volume : Measure (ℝ × ℝ)) := by
    intro x
    exact generalizedMatrixEnergy_integrable hτ hα one_pos hpq hgap hαβ x
  have hnorm : ∀ x, ∫ z, fiberEnergy x z ∂(volume : Measure (ℝ × ℝ)) = ‖x‖ ^ 2 := by
    intro x
    rw [show (∫ z, fiberEnergy x z ∂(volume : Measure (ℝ × ℝ))) =
        rationalZakEta α p q * ∫ z, ∑ r : Fin p,
          ‖rationalPositiveFiberField hα one_pos hpq hgap hαβ x z r‖ ^ 2
          ∂(volume : Measure (ℝ × ℝ)) by
      simp [fiberEnergy, integral_const_mul]]
    rw [rationalPositiveFiberField_component_energy_identity_scaled
      hα one_pos hpq hgap hαβ x]
    field_simp [ne_of_gt (rationalZakEta_pos hα one_pos hgap hαβ)]
  have hcoeff : ∀ x,
      generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α 1 x =
        ∫ z, matrixEnergy x z ∂(volume : Measure (ℝ × ℝ)) := by
    intro x
    exact rationalPositiveGammaMatrix_coeff_identity
      hα one_pos hpq hgap hαβ x
  have hbounds := Zak.coefficient_bounds_of_ae_integral_transfer
    (X := Lp ℂ 2 (volume : Measure ℝ))
    (lower := lower) (upper := upper)
    (coeffEnergy := generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α 1)
    (fiberEnergy := fiberEnergy) (matrixEnergy := matrixEnergy)
    (volume : Measure (ℝ × ℝ)) hlower hle hfiber_int hmatrix_int hnorm hcoeff
    (fun x ↦ Filter.Eventually.of_forall fun z ↦ (hpoint x z).1)
    (fun x ↦ Filter.Eventually.of_forall fun z ↦ (hpoint x z).2)
  rcases hbounds with ⟨A, B, hA, hAB, hineq⟩
  refine ⟨A, B, hA, hAB, ?_⟩
  intro x
  have hsum : Summable fun mn : ℤ × ℤ =>
      ‖inner ℂ x (generalizedH1ElementLp τ hτ α 1 mn.1 mn.2)‖ ^ 2 := by
    by_cases hx : x = 0
    · subst x
      simp
    · refine summable_of_pos_le_tsum ?_ (hineq x).1
      exact mul_pos hA (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
  constructor
  · calc
      A * ‖x‖ ^ 2 ≤ generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α 1 x := (hineq x).1
      _ = ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ x (generalizedH1ElementLp τ hτ α 1 m n)‖ ^ 2 := by
        exact hsum.tsum_prod
  · calc
      (∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ x (generalizedH1ElementLp τ hτ α 1 m n)‖ ^ 2) =
          generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α 1 x := hsum.tsum_prod.symm
      _ ≤ B * ‖x‖ ^ 2 := (hineq x).2

end LyubarskiiNes.GeneralLattice
