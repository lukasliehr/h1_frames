import LeanCode.RationalDensity.RationalPositive.GammaCoeffWork
import LeanCode.FrobeniusDeterminant.PrimitiveDerivativeSkeleton

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- Nonzero cyclic consecutive minor for the paper-side rational-Zak matrix at
every point of the fundamental frequency plane, reduced to the primitive
theta-derivative cyclic-minor theorem by the closed first-Hermite Zak formula
and diagonal determinant scaling. -/
theorem rationalZakPMatrixH1_cyclic_minor_nonzero
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ z : ℝ × ℝ, ∃ j : Fin q,
      ((rationalZakPMatrixH1 α p q z).submatrix id
        (LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j)).det ≠ 0 := by
  intro z
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq : 0 < q := q_pos_of_gap hgap
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  let γ : ℝ := rationalZakGamma α q
  let τ : ℂ := gaussianZakTau γ
  let lam : ℂ := (γ : ℂ) * (z.2 : ℂ)
  let a : ℂ := (γ : ℂ)⁻¹ * (z.1 : ℂ) + Complex.I * (z.2 : ℂ) / (γ : ℂ)
  rcases LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix_cyclic_minor_nonzero
      (p := p) (q := q) hp hpq_coprime hgap τ a lam (by
        dsimp [τ, γ]
        simpa [gaussianZakTau] using gaussianZakTau_im_pos hγ) with
    ⟨j, hdet⟩
  refine ⟨j, ?_⟩
  let rows := LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j
  let A : Matrix (Fin p) (Fin p) ℂ :=
    (LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix p q τ lam a).submatrix rows id
  let B : Matrix (Fin p) (Fin p) ℂ :=
    (rationalZakPMatrixH1 α p q z).submatrix id rows
  let C : ℂ := -Complex.I / (γ : ℂ) ^ 2 *
    Complex.exp (-(Real.pi : ℂ) * (z.2 : ℂ) ^ 2)
  let rowScale : Fin p → ℂ := fun s => C * gaussianZakPhase z.2
    (z.1 + γ * ((s : ℕ) : ℝ) / (p : ℝ))
  let colScale : Fin p → ℂ := fun r => gaussianZakPhase z.2 (α * ((rows r : Fin q) : ℕ))
  have hentry : ∀ s r, B s r = rowScale s * A r s * colScale r := by
    intro s r
    dsimp [B, A, rowScale, colScale, C, rows, γ, τ, lam, a]
    rw [rationalZakPMatrixH1_eq_scaled_primitive (hα := hα)
      (hformula := gaussianZakH1_formula_of_h0_and_deriv_bridge
        gaussianZakH0_transform_formula gaussianZakH1_deriv_bridge)]
    have hphase :
        gaussianZakPhase z.2
          (z.1 + α * (((LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j r : Fin q) : ℕ) : ℝ) +
            rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) =
        gaussianZakPhase z.2
            (z.1 + rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) *
          gaussianZakPhase z.2
            (α * (((LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j r : Fin q) : ℕ) : ℝ)) := by
      calc
        gaussianZakPhase z.2
          (z.1 + α * (((LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j r : Fin q) : ℕ) : ℝ) +
            rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ))
            = gaussianZakPhase z.2
                ((z.1 + rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) +
                  α * (((LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j r : Fin q) : ℕ) : ℝ)) := by
                congr 1
                ring
        _ = gaussianZakPhase z.2
              (z.1 + rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) *
            gaussianZakPhase z.2
              (α * (((LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j r : Fin q) : ℕ) : ℝ)) :=
            gaussianZakPhase_add z.2 _ _
    rw [hphase]
    ring
  have hB : B = Matrix.diagonal rowScale * A.transpose * Matrix.diagonal colScale :=
    matrix_eq_scaled_transpose_of_apply A B rowScale colScale hentry
  have hrow : ∀ s, rowScale s ≠ 0 := by
    intro s
    dsimp [rowScale, C]
    apply mul_ne_zero
    · apply mul_ne_zero
      · have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hγ
        exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero 2 hγc)
      · exact Complex.exp_ne_zero _
    · exact gaussianZakPhase_ne_zero _ _
  have hcol : ∀ r, colScale r ≠ 0 := by
    intro r
    exact gaussianZakPhase_ne_zero _ _
  exact det_ne_zero_of_scaled_transpose A B rowScale colScale hrow hcol hB hdet

/-- Nonzero cyclic consecutive minor for the concrete adjoint-oriented
rational-Zak matrix at every point, transferred from the paper-side matrix by
conjugate-transpose determinant bookkeeping. -/
theorem rationalZakMatrix_cyclic_minor_nonzero
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ z : ℝ × ℝ, ∃ j : Fin q,
      ((rationalZakMatrix α p q z).submatrix
        (LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j) id).det ≠ 0 := by
  intro z
  rcases rationalZakPMatrixH1_cyclic_minor_nonzero hα hβ hpq_coprime hgap hαβ z with
    ⟨j, hdet⟩
  refine ⟨j, ?_⟩
  let rows := LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j
  have hsub :
      ((rationalZakMatrix α p q z).submatrix rows id) =
        ((rationalZakPMatrixH1 α p q z).submatrix id rows)ᴴ := by
    ext r s
    simp [rationalZakMatrix, rows]
  rw [hsub, Matrix.det_conjTranspose]
  exact (star_ne_zero).2 hdet

/-- The concrete adjoint-oriented rational-Zak matrix has global two-sided
operator bounds. This packages only matrix facts: closed-form continuity,
cyclic-minor injectivity, compact-periodic lower bound, and entrywise upper
bound. It deliberately avoids the rational fiber-field `MemLp` and norm
identity packages. -/
theorem rationalZakMatrix_uniform_bounds
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      (∀ z w, A * ‖w‖ ^ 2 ≤ ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2) ∧
      (∀ z w, ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2) := by
  classical
  have hq : 0 < q := q_pos_of_gap hgap
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  have hformula : ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH1C x ω = gaussianZakH1ClosedForm γ ω x :=
    gaussianZakH1_formula_of_h0_and_deriv_bridge
      gaussianZakH0_transform_formula gaussianZakH1_deriv_bridge
  have hclosed :
      ∀ z s t,
        rationalZakPMatrixH1 α p q z s t =
          gaussianZakH1ClosedForm (rationalZakGamma α q) z.2
            (z.1 + α * ((t : ℕ) : ℝ) +
              rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) :=
    rationalZakPMatrixH1_closedForm_of_gaussianZakH1 hformula hγ
  have hP_cont : Continuous (rationalZakPMatrixH1 α p q) :=
    continuous_rationalZakPMatrixH1_of_closedForm hγ hclosed
  have hM_cont : Continuous (rationalZakMatrix α p q) := by
    change Continuous (fun z => (rationalZakPMatrixH1 α p q z)ᴴ)
    exact continuous_conjTranspose_matrix_field (P := rationalZakPMatrixH1 α p q) hP_cont
  have hminor :=
    rationalZakMatrix_cyclic_minor_nonzero hα hβ hpq_coprime hgap hαβ
  have hinj : ∀ z, Function.Injective (rationalZakMatrix α p q z).mulVec :=
    rationalZakMatrix_injective_of_cyclic_minor_field hminor
  rcases rationalZakMatrix_uniform_lower_bound_of_injective hγ hM_cont hinj
      (fin_complex_unit_sphere_nonempty hp) with
    ⟨A, hA, hlower⟩
  have hP_entry_bdd :
      ∀ i j, ∃ Cij : ℝ, ∀ z, ‖rationalZakPMatrixH1 α p q z i j‖ ≤ Cij :=
    rationalZakPMatrixH1_entries_bounded_of_continuous hγ hP_cont
  have hentry_bdd : ∀ i j, ∃ Cij : ℝ, ∀ z, ‖rationalZakMatrix α p q z i j‖ ≤ Cij := by
    change ∀ i j, ∃ Cij : ℝ, ∀ z, ‖(rationalZakPMatrixH1 α p q z)ᴴ i j‖ ≤ Cij
    exact conjTranspose_matrix_field_entries_bounded (P := rationalZakPMatrixH1 α p q)
      hP_entry_bdd
  let Cij : Fin q → Fin p → ℝ := fun i j => Classical.choose (hentry_bdd i j)
  let C : ℝ := ∑ ij : Fin q × Fin p, max 0 (Cij ij.1 ij.2)
  have hC : 0 ≤ C := by
    exact Finset.sum_nonneg fun ij _hij => le_max_left 0 (Cij ij.1 ij.2)
  have hentry : ∀ z i j, ‖rationalZakMatrix α p q z i j‖ ≤ C := by
    intro z i j
    have hCij := Classical.choose_spec (hentry_bdd i j) z
    have hterm_le : max 0 (Cij i j) ≤ C := by
      exact Finset.single_le_sum
        (by intro ij _hij; exact le_max_left 0 (Cij ij.1 ij.2))
        (Finset.mem_univ (i, j))
    exact le_trans (le_trans hCij (le_max_right 0 (Cij i j))) hterm_le
  rcases rationalZakMatrix_uniform_upper_bound_of_entry_bound
      (p := p) (q := q) (rationalZakMatrix α p q) hC hentry with
    ⟨B₀, _hB₀_nonneg, hupper₀⟩
  let B : ℝ := max A B₀
  refine ⟨A, B, hA, le_max_left A B₀, hlower, ?_⟩
  intro z w
  calc
    ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2 ≤ B₀ * ‖w‖ ^ 2 := hupper₀ z w
    _ ≤ B * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right A B₀) (sq_nonneg ‖w‖)

/-- Euclidean corrected-matrix energy: the component squared norm of the
student-corrected matrix output.  This is the coefficient identity's correct
finite-dimensional energy; the old finite-function norm was Lean's sup norm. -/
noncomputable def rationalPositiveCorrectedMatrixEuclideanEnergy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : ℝ :=
  rationalPositiveCorrectedCoeffScale α p q *
    ∑ t : Fin q,
      ‖(rationalPositiveCorrectedZakMatrix α p q z *ᵥ
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2

/-- The corresponding Euclidean gamma-fiber energy with prefactor `η γ`. -/
noncomputable def rationalPositiveGammaMatrixEuclideanEnergy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : ℝ :=
  rationalZakEta α p q * rationalZakGamma α q *
    ∑ t : Fin q,
      ‖(rationalZakMatrix α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2

/-- Pointwise equality between the gamma Euclidean energy and the corrected
matrix Euclidean energy. -/
lemma rationalPositiveGammaMatrixEuclideanEnergy_eq_corrected
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) :
    rationalPositiveGammaMatrixEuclideanEnergy hα hβ hpq_coprime hgap hαβ x z =
      rationalPositiveCorrectedMatrixEuclideanEnergy hα hβ hpq_coprime hgap hαβ x z := by
  let D := rationalPositiveFourierRowChange α p q z
  let P := rationalZakMatrix α p q z
  let v := rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z
  let y : Fin q → ℂ := P *ᵥ (Dᴴ *ᵥ v)
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp_nat
  have hmul :
      P *ᵥ (((p : ℂ)⁻¹) • (Dᴴ *ᵥ v)) = ((p : ℂ)⁻¹) • y := by
    simpa [y] using Matrix.mulVec_smul P ((p : ℂ)⁻¹) (Dᴴ *ᵥ v)
  have hnorm_inv : ‖((p : ℂ)⁻¹)‖ ^ 2 = ((p : ℝ) ^ 2)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
    field_simp [ne_of_gt hp_real]
  have hsum :
      (∑ t : Fin q,
        ‖(P *ᵥ (((p : ℂ)⁻¹) • (Dᴴ *ᵥ v))) t‖ ^ 2) =
        ((p : ℝ) ^ 2)⁻¹ * ∑ t : Fin q, ‖y t‖ ^ 2 := by
    calc
      (∑ t : Fin q,
          ‖(P *ᵥ (((p : ℂ)⁻¹) • (Dᴴ *ᵥ v))) t‖ ^ 2) =
          ∑ t : Fin q, ‖(((p : ℂ)⁻¹) • y) t‖ ^ 2 := by
            rw [hmul]
      _ = ∑ t : Fin q, ‖((p : ℂ)⁻¹)‖ ^ 2 * ‖y t‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            simp [Pi.smul_apply]
            ring
      _ = ‖((p : ℂ)⁻¹)‖ ^ 2 * ∑ t : Fin q, ‖y t‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ = ((p : ℝ) ^ 2)⁻¹ * ∑ t : Fin q, ‖y t‖ ^ 2 := by
            rw [hnorm_inv]
  have hmatrix :
      rationalPositiveCorrectedZakMatrix α p q z *ᵥ
          rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z =
        y := by
    simp [rationalPositiveCorrectedZakMatrix, D, P, v, y, Matrix.mulVec_mulVec]
  calc
    rationalPositiveGammaMatrixEuclideanEnergy hα hβ hpq_coprime hgap hαβ x z =
        (rationalZakEta α p q * rationalZakGamma α q) *
          (((p : ℝ) ^ 2)⁻¹ * ∑ t : Fin q, ‖y t‖ ^ 2) := by
          simp [rationalPositiveGammaMatrixEuclideanEnergy,
            rationalPositiveGammaFiberField, D, P, v, y, hsum]
    _ = rationalPositiveCorrectedCoeffScale α p q *
          ∑ t : Fin q, ‖y t‖ ^ 2 := by
          simp [rationalPositiveCorrectedCoeffScale]
          field_simp [pow_ne_zero 2 (ne_of_gt hp_real)]
    _ = rationalPositiveCorrectedMatrixEuclideanEnergy hα hβ hpq_coprime hgap hαβ x z := by
          simp [rationalPositiveCorrectedMatrixEuclideanEnergy, hmatrix]

theorem rationalPositiveGammaMatrixEuclideanEnergy_integrable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      Integrable
        (fun z : ℝ × ℝ =>
          rationalPositiveGammaMatrixEuclideanEnergy
            hα hβ hpq_coprime hgap hαβ x z)
        (volume : Measure (ℝ × ℝ)) := by
  intro x
  have hmem := (matrixGammaFiber_memLp hα hβ hpq_coprime hgap hαβ x).continuousLinearMap_comp
    (toEuclidCLM q)
  have hsum : Integrable (fun z : ℝ × ℝ =>
      ∑ t : Fin q, ‖(rationalZakMatrix α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    refine (hmem.integrable_norm_pow (p := 2) (by norm_num)).congr ?_
    filter_upwards with z
    exact norm_toEuclidCLM_sq q _
  simpa [rationalPositiveGammaMatrixEuclideanEnergy] using
    hsum.const_mul (rationalZakEta α p q * rationalZakGamma α q)

theorem rationalPositiveCorrectedMatrixEuclideanEnergy_integrable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      Integrable
        (fun z : ℝ × ℝ =>
          rationalPositiveCorrectedMatrixEuclideanEnergy
            hα hβ hpq_coprime hgap hαβ x z)
        (volume : Measure (ℝ × ℝ)) := by
  intro x
  exact (rationalPositiveGammaMatrixEuclideanEnergy_integrable
    hα hβ hpq_coprime hgap hαβ x).congr
    (Filter.Eventually.of_forall fun z =>
      rationalPositiveGammaMatrixEuclideanEnergy_eq_corrected
        hα hβ hpq_coprime hgap hαβ x z)

theorem rationalPositiveCorrectedMatrixEuclidean_coeff_identity
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    (∀ x : Lp ℂ 2 (volume : Measure ℝ), productCoeffEnergy α β x =
      ∫ z, rationalPositiveCorrectedMatrixEuclideanEnergy
        hα hβ hpq_coprime hgap hαβ x z
        ∂(volume : Measure (ℝ × ℝ))) := by
  intro x
  calc
    productCoeffEnergy α β x =
        gammaMatrixEuclideanEnergyIntegral hα hβ hpq_coprime hgap hαβ x :=
          rationalPositiveGammaMatrix_coeff_identity
            hα hβ hpq_coprime hgap hαβ x
    _ = ∫ z, rationalPositiveGammaMatrixEuclideanEnergy
          hα hβ hpq_coprime hgap hαβ x z
          ∂(volume : Measure (ℝ × ℝ)) := by
          rfl
    _ = ∫ z, rationalPositiveCorrectedMatrixEuclideanEnergy
          hα hβ hpq_coprime hgap hαβ x z
          ∂(volume : Measure (ℝ × ℝ)) := by
          exact integral_congr_ae
            (Filter.Eventually.of_forall fun z =>
              rationalPositiveGammaMatrixEuclideanEnergy_eq_corrected
                hα hβ hpq_coprime hgap hαβ x z)

/-- Euclidean corrected coefficient-transfer data for the shifted honest fiber.
The pointwise lower/upper bounds are the old sup-norm bounds plus the
finite-dimensional equivalence `‖y‖² ≤ Σ |yᵢ|² ≤ q‖y‖²`. -/
theorem rationalPositiveCorrectedMatrixEuclidean_energy_transfer_data
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      (∀ x : Lp ℂ 2 (volume : Measure ℝ),
        Integrable
          (fun z : ℝ × ℝ =>
            rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z)
          (volume : Measure (ℝ × ℝ))) ∧
      (∀ x : Lp ℂ 2 (volume : Measure ℝ), productCoeffEnergy α β x =
        ∫ z, rationalPositiveCorrectedMatrixEuclideanEnergy
          hα hβ hpq_coprime hgap hαβ x z
          ∂(volume : Measure (ℝ × ℝ))) ∧
      (∀ x : Lp ℂ 2 (volume : Measure ℝ),
        ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
          A * (∑ r : Fin p,
            ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) ≤
            rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z) ∧
      (∀ x : Lp ℂ 2 (volume : Measure ℝ),
        ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
          rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z ≤
            B * (∑ r : Fin p,
              ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)) := by
  rcases rationalZakMatrix_uniform_bounds hα hβ hpq_coprime hgap hαβ with
    ⟨A, B, hA, hAB, hP_lower, hP_upper⟩
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp_nat
  rcases LyubarskiiNes.RationalDensity.rationalPositiveFourierRowChange_conjTranspose_exists_lower_bound
      α q hp_nat with
    ⟨c, hc, hD_lower⟩
  let scale : ℝ := rationalPositiveCorrectedCoeffScale α p q
  let lower : ℝ := scale * ((A * c) / (p : ℝ))
  let upper0 : ℝ := scale * ((q : ℝ) * (B * (p : ℝ) ^ 2))
  let upper : ℝ := max upper0 lower
  have hscale_pos : 0 < scale := by
    simpa [scale] using rationalPositiveCorrectedCoeffScale_pos hα hβ hgap hαβ
  have hcore_pos : 0 < (A * c) / (p : ℝ) := div_pos (mul_pos hA hc) hp_real
  have hlower_pos : 0 < lower := mul_pos hscale_pos hcore_pos
  have hlower_le_upper : lower ≤ upper := le_max_right upper0 lower
  have hupper0_le_upper : upper0 ≤ upper := le_max_left upper0 lower
  have hB_nonneg : 0 ≤ B := le_trans hA.le hAB
  refine ⟨lower, upper, hlower_pos, hlower_le_upper,
    rationalPositiveCorrectedMatrixEuclideanEnergy_integrable
      hα hβ hpq_coprime hgap hαβ,
    rationalPositiveCorrectedMatrixEuclidean_coeff_identity
      hα hβ hpq_coprime hgap hαβ, ?_, ?_⟩
  · intro x
    exact Filter.Eventually.of_forall fun z => by
      let v : Fin p → ℂ :=
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z
      let y : Fin q → ℂ :=
        rationalPositiveCorrectedZakMatrix α p q z *ᵥ v
      let CE : ℝ := ∑ r : Fin p, ‖v r‖ ^ 2
      let Ncorr : ℝ := ‖y‖ ^ 2
      let Esum : ℝ := ∑ t : Fin q, ‖y t‖ ^ 2
      have hbase : ((A * c) / (p : ℝ)) * CE ≤ Ncorr := by
        simpa [CE, Ncorr, y, v] using
          LyubarskiiNes.RationalDensity.rationalPositiveCorrectedZakMatrix_lower_component_energy
            hα hβ hpq_coprime hgap hαβ hA hc x z hP_lower hD_lower
      have hsum : Ncorr ≤ Esum := by
        simpa [Ncorr, Esum, y] using finiteVector_norm_sq_le_sum_norm_sq y
      calc
        lower * CE = scale * (((A * c) / (p : ℝ)) * CE) := by
          dsimp [lower]
          ring
        _ ≤ scale * Ncorr := mul_le_mul_of_nonneg_left hbase hscale_pos.le
        _ ≤ scale * Esum := mul_le_mul_of_nonneg_left hsum hscale_pos.le
        _ = rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z := by
          simp [rationalPositiveCorrectedMatrixEuclideanEnergy, scale, Esum, y, v]
  · intro x
    exact Filter.Eventually.of_forall fun z => by
      let v : Fin p → ℂ :=
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z
      let y : Fin q → ℂ :=
        rationalPositiveCorrectedZakMatrix α p q z *ᵥ v
      let CE : ℝ := ∑ r : Fin p, ‖v r‖ ^ 2
      let Ncorr : ℝ := ‖y‖ ^ 2
      let Esum : ℝ := ∑ t : Fin q, ‖y t‖ ^ 2
      have hCE_nonneg : 0 ≤ CE := by
        exact Finset.sum_nonneg fun r _hr => sq_nonneg _
      have hbase : Ncorr ≤ (B * (p : ℝ) ^ 2) * CE := by
        simpa [CE, Ncorr, y, v] using
          rationalPositiveCorrectedZakMatrix_upper_component_energy
            hα hβ hpq_coprime hgap hαβ hB_nonneg x z hP_upper
      have hsum : Esum ≤ (q : ℝ) * Ncorr := by
        simpa [Ncorr, Esum, y] using finiteVector_sum_norm_sq_le_card_mul_norm_sq y
      calc
        rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z =
            scale * Esum := by
          simp [rationalPositiveCorrectedMatrixEuclideanEnergy, scale, Esum, y, v]
        _ ≤ scale * ((q : ℝ) * Ncorr) :=
            mul_le_mul_of_nonneg_left hsum hscale_pos.le
        _ ≤ scale * ((q : ℝ) * ((B * (p : ℝ) ^ 2) * CE)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg q))
              hscale_pos.le
        _ = upper0 * CE := by
          dsimp [upper0]
          ring
        _ ≤ upper * CE := mul_le_mul_of_nonneg_right hupper0_le_upper hCE_nonneg

/-- Rectangle-energy transfer data derived from the narrower matrix-fiber
residual. -/
theorem rational_positive_coefficient_transfer_data
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      ∃ fiberEnergy matrixEnergy :
          Lp ℂ 2 (volume : Measure ℝ) → ℝ × ℝ → ℝ,
        (∀ x, Integrable (fiberEnergy x) (volume : Measure (ℝ × ℝ))) ∧
        (∀ x, Integrable (matrixEnergy x) (volume : Measure (ℝ × ℝ))) ∧
        (∀ x, (∫ z, fiberEnergy x z ∂(volume : Measure (ℝ × ℝ))) = ‖x‖ ^ 2) ∧
        (∀ x, productCoeffEnergy α β x =
          ∫ z, matrixEnergy x z ∂(volume : Measure (ℝ × ℝ))) ∧
        (∀ x, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
          A * fiberEnergy x z ≤ matrixEnergy x z) ∧
        (∀ x, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
          matrixEnergy x z ≤ B * fiberEnergy x z) := by
  have hq : 0 < q := q_pos_of_gap hgap
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  rcases rationalPositiveCorrectedMatrixEuclidean_energy_transfer_data
      hα hβ hpq_coprime hgap hαβ with
    ⟨A0, B0, hA0, hA0B0, hmatrix_int, hcoeff, hpt_lower0, hpt_upper0⟩
  let η : ℝ := rationalZakEta α p q
  let lower : ℝ := A0 / η
  let upper : ℝ := max (B0 / η) lower
  have hη_pos : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have hlower_pos : 0 < lower := div_pos hA0 hη_pos
  have hlower_le_upper : lower ≤ upper := le_max_right (B0 / η) lower
  have hB0_div_le_upper : B0 / η ≤ upper := le_max_left (B0 / η) lower
  have hB0_le_upper_mul_eta : B0 ≤ upper * η := by
    exact (div_le_iff₀ hη_pos).1 hB0_div_le_upper
  refine ⟨lower, upper, hlower_pos, hlower_le_upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x z =>
      η * (∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
  · exact fun x z =>
      rationalPositiveCorrectedMatrixEuclideanEnergy hα hβ hpq_coprime hgap hαβ x z
  · intro x
    exact (rationalPositiveFiberField_component_energy_integrable_from_lintegral
      hα hβ hpq_coprime hgap hαβ x).const_mul η
  · exact hmatrix_int
  · intro x
    calc
      (∫ z : ℝ × ℝ,
          η * (∑ r : Fin p,
            ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
          ∂(volume : Measure (ℝ × ℝ))) =
          η * (∫ z : ℝ × ℝ,
            (∑ r : Fin p,
              ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
            ∂(volume : Measure (ℝ × ℝ))) := by
            rw [MeasureTheory.integral_const_mul]
      _ = η * (η⁻¹ * ‖x‖ ^ 2) := by
            rw [rationalPositiveFiberField_component_energy_identity_scaled
              hα hβ hpq_coprime hgap hαβ x]
      _ = ‖x‖ ^ 2 := by
            field_simp [hη_ne]
  · exact hcoeff
  · intro x
    exact (hpt_lower0 x).mono fun z hz => by
      let componentEnergy : ℝ :=
        ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2
      have hscale :
          lower * (η * componentEnergy) = A0 * componentEnergy := by
        calc
          lower * (η * componentEnergy) =
              (A0 / η) * (η * componentEnergy) := rfl
          _ = A0 * componentEnergy := by
              field_simp [hη_ne]
      calc
        lower * (η * componentEnergy) = A0 * componentEnergy := hscale
        _ ≤ rationalPositiveCorrectedMatrixEuclideanEnergy
              hα hβ hpq_coprime hgap hαβ x z := by
            simpa [componentEnergy] using hz
  · intro x
    exact (hpt_upper0 x).mono fun z hz => by
      let componentEnergy : ℝ :=
        ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2
      have hcomponent_nonneg : 0 ≤ componentEnergy := by
        exact Finset.sum_nonneg fun r _hr => sq_nonneg _
      have hscaled :
          B0 * componentEnergy ≤ upper * (η * componentEnergy) := by
        calc
          B0 * componentEnergy ≤ (upper * η) * componentEnergy :=
            mul_le_mul_of_nonneg_right hB0_le_upper_mul_eta hcomponent_nonneg
          _ = upper * (η * componentEnergy) := by ring
      exact le_trans (by
        simpa [componentEnergy] using hz) hscaled

/-- Product-indexed coefficient bounds for the paper's positive rational-density
theorem, derived from the narrower rectangle-energy transfer data above. -/
theorem rational_positive_product_coeff_bounds
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      A * ‖x‖ ^ 2 ≤
          ∑' mn : ℤ × ℤ,
            ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2
        ∧
      ∑' mn : ℤ × ℤ,
          ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2
        ≤ B * ‖x‖ ^ 2 := by
  rcases rational_positive_coefficient_transfer_data
      hα hβ hpq_coprime hgap hαβ with
    ⟨A, B, hA, hAB, fiberEnergy, matrixEnergy, hfiber_int, hmatrix_int,
      hnorm, hcoeff, hpt_lower, hpt_upper⟩
  have hbounds := Zak.coefficient_bounds_of_ae_integral_transfer
    (X := Lp ℂ 2 (volume : Measure ℝ))
    (Ω := ℝ × ℝ)
    (μ := (volume : Measure (ℝ × ℝ)))
    (lower := A) (upper := B)
    (coeffEnergy := productCoeffEnergy α β)
    (fiberEnergy := fiberEnergy)
    (matrixEnergy := matrixEnergy)
    hA hAB hfiber_int hmatrix_int hnorm hcoeff hpt_lower hpt_upper
  rcases hbounds with ⟨A', B', hA', hAB', hineq⟩
  refine ⟨A', B', hA', hAB', ?_⟩
  intro x
  simpa [productCoeffEnergy] using hineq x

/-- Product-indexed coefficient bound data for the paper's positive
rational-density theorem, including genuine summability of the product-indexed
coefficient series.

This theorem narrows the source analytic axiom to the lower/upper product
coefficient bounds: for nonzero `x`, the positive lower bound rules out the
nonsummable real-`tsum = 0` convention; for `x = 0`, summability is immediate. -/
theorem rational_positive_product_coeff_bounds_with_summability
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      Summable (fun mn : ℤ × ℤ =>
          ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2)
        ∧
      A * ‖x‖ ^ 2 ≤
          ∑' mn : ℤ × ℤ,
            ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2
        ∧
      ∑' mn : ℤ × ℤ,
          ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2
        ≤ B * ‖x‖ ^ 2 := by
  rcases rational_positive_product_coeff_bounds
      hα hβ hpq_coprime hgap hαβ with
    ⟨A, B, hA, hAB, hineq⟩
  refine ⟨A, B, hA, hAB, ?_⟩
  intro x
  have hsum : Summable fun mn : ℤ × ℤ =>
      ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2 := by
    by_cases hx : x = 0
    · subst x
      simp
    · refine summable_of_pos_le_tsum ?_ (hineq x).1
      exact mul_pos hA (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
  exact ⟨hsum, (hineq x).1, (hineq x).2⟩

/-- The paper's positive rational-density theorem for `h₁`, reduced to the
product-indexed coefficient bounds supplied by the Zak/rank analysis. -/
theorem rational_positive
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    LyubarskiiNes.IsGaborFrame α β := by
  rcases rational_positive_product_coeff_bounds_with_summability
      hα hβ hpq_coprime hgap hαβ with
    ⟨A, B, hA, hAB, hineq⟩
  refine ⟨A, B, hA, hAB, ?_⟩
  intro x
  have hsum : Summable fun mn : ℤ × ℤ =>
      ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2 :=
    (hineq x).1
  constructor
  · calc
      A * ‖x‖ ^ 2 ≤
          ∑' mn : ℤ × ℤ,
            ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2 :=
        (hineq x).2.1
      _ = ∑' (m : ℤ) (n : ℤ),
            ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β m n)‖ ^ 2 := by
        exact hsum.tsum_prod
  · calc
      (∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β m n)‖ ^ 2)
          = ∑' mn : ℤ × ℤ,
              ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2 := by
        exact hsum.tsum_prod.symm
      _ ≤ B * ‖x‖ ^ 2 :=
        (hineq x).2.2

end LyubarskiiNes.RationalDensity
