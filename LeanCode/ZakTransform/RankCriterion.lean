import LeanCode.ZakTransform.Fiberization

open scoped Matrix ComplexOrder
open MeasureTheory

namespace Zak

section RankCriterion

/-- A matrix has full column rank exactly when its `mulVec` map is injective. -/
lemma mulVec_injective_iff_rank_eq_card_width {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) :
    Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  constructor
  · intro hA
    have hlin : Function.Injective A.mulVecLin := by
      intro x y hxy
      exact hA hxy
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hlin, Module.finrank_pi]
  · intro hA
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [← Matrix.rank, hA, Module.finrank_pi] at hsum
    have hkerFin : Module.finrank ℂ (LinearMap.ker A.mulVecLin) = 0 := by
      omega
    have hker : LinearMap.ker A.mulVecLin = ⊥ := by
      exact Submodule.finrank_eq_zero.mp hkerFin
    have hlin : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hker
    intro x y hxy
    exact hlin hxy

/-- The quadratic form of a Gram matrix is the squared dot product of the
image under the original matrix. -/
lemma gram_quadratic_eq_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

/-- Each coordinate of a finite function is bounded by the default finite
sup-norm. -/
lemma pi_norm_apply_le_norm {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (i : ι) :
    ‖v i‖ ≤ ‖v‖ := by
  rw [Pi.norm_def]
  exact_mod_cast
    Finset.le_sup (s := Finset.univ) (f := fun b => ‖v b‖₊)
      (Finset.mem_univ i)

/-- To bound a finite function in Lean's default finite sup-norm, it suffices
to bound every coordinate. -/
lemma pi_norm_le_of_forall_norm_le {ι : Type*} [Fintype ι]
    (v : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ‖v i‖ ≤ C) :
    ‖v‖ ≤ C := by
  rw [Pi.norm_def]
  rw [← NNReal.coe_mk C hC]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le_iff.mpr
  intro i _hi
  rw [← NNReal.coe_le_coe]
  simpa using hv i

/-- The Euclidean dot-product energy of a finite vector is controlled by the
default finite sup-norm. This is the norm-equivalence bridge needed when Gram
matrix positivity is used to prove estimates stated with Lean's `Pi` norm. -/
lemma re_dotProduct_star_self_le_card_mul_norm_sq {ι : Type*} [Fintype ι]
    (v : ι → ℂ) :
    (star v ⬝ᵥ v).re ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
  calc
    (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
      simp [dotProduct, RCLike.norm_sq_eq_def]
    _ ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ (norm_nonneg _) (pi_norm_apply_le_norm v i) 2
    _ = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
      simp

/-- A finite Gram matrix is positive definite exactly when the original matrix has full column rank. -/
theorem posDef_bound_iff_full_rank {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    (Aᴴ * A).PosDef ↔ A.rank = Fintype.card n := by
  constructor
  · intro hA
    have hunit : IsUnit (Aᴴ * A) := hA.isUnit
    have hrankGram : (Aᴴ * A).rank = Fintype.card n := Matrix.rank_of_isUnit _ hunit
    exact (Matrix.rank_conjTranspose_mul_self A).symm.trans hrankGram
  · intro hA
    exact Matrix.PosDef.conjTranspose_mul_self A
      ((mulVec_injective_iff_rank_eq_card_width A).2 hA)

/-- Gram positive-definiteness is equivalently injectivity of the matrix
`mulVec` map. This is often the most convenient form for lower-frame-bound
arguments. -/
lemma gram_posDef_iff_mulVec_injective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    (Aᴴ * A).PosDef ↔ Function.Injective A.mulVec := by
  rw [posDef_bound_iff_full_rank A]
  exact (mulVec_injective_iff_rank_eq_card_width A).symm

/-- Backward direction of `gram_posDef_iff_mulVec_injective`. -/
lemma gram_posDef_of_mulVec_injective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : Function.Injective A.mulVec) :
    (Aᴴ * A).PosDef :=
  (gram_posDef_iff_mulVec_injective A).2 hA

/-- A positive-definite finite matrix has a strictly positive quadratic-form
minimum on the unit sphere.  The nonemptiness hypothesis keeps the statement
usable for later finite-dimensional Zak fibers without choosing coordinates
here. -/
lemma posDef_exists_pos_lower_bound_on_unit_sphere {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) (hG : G.PosDef)
    (hsphere : (Metric.sphere (0 : n → ℂ) 1).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℂ, x ∈ Metric.sphere (0 : n → ℂ) 1 →
      c ≤ RCLike.re (star x ⬝ᵥ (G *ᵥ x)) := by
  let q : (n → ℂ) → ℝ := fun x => RCLike.re (star x ⬝ᵥ (G *ᵥ x))
  have hcompact : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere _ _
  have hcont : Continuous q := by
    unfold q
    fun_prop
  obtain ⟨x0, hx0, hx0_min⟩ := hcompact.exists_isMinOn hsphere hcont.continuousOn
  refine ⟨q x0, ?_, ?_⟩
  · have hx0_ne : x0 ≠ 0 := by
      intro hxzero
      have hdist : dist x0 (0 : n → ℂ) = 1 := by
        simpa [Metric.mem_sphere] using hx0
      have : (0 : ℝ) = 1 := by
        simp [hxzero] at hdist
      norm_num at this
    exact hG.re_dotProduct_pos hx0_ne
  · intro x hx
    exact hx0_min hx

/-- Gram-matrix version of the compact unit-sphere lower bound. -/
lemma gram_posDef_exists_pos_lower_bound_on_unit_sphere {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n ℂ) (hA : (Aᴴ * A).PosDef)
    (hsphere : (Metric.sphere (0 : n → ℂ) 1).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℂ, x ∈ Metric.sphere (0 : n → ℂ) 1 →
      c ≤ RCLike.re (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)) :=
  posDef_exists_pos_lower_bound_on_unit_sphere (Aᴴ * A) hA hsphere

/-- A lower bound for `‖A *ᵥ x‖ ^ 2` on the unit sphere extends
homogeneously to every vector. -/
lemma mulVec_norm_sq_lower_bound_of_unit_sphere {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) {c : ℝ}
    (hunit : ∀ x : n → ℂ, x ∈ Metric.sphere (0 : n → ℂ) 1 → c ≤ ‖A *ᵥ x‖ ^ 2) :
    ∀ x : n → ℂ, c * ‖x‖ ^ 2 ≤ ‖A *ᵥ x‖ ^ 2 := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let y : n → ℂ := (↑‖x‖ : ℂ)⁻¹ • x
    have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxnorm_ne_real : ‖x‖ ≠ 0 := ne_of_gt hxnorm_pos
    have hy_norm : ‖y‖ = 1 := by
      calc
        ‖y‖ = ‖(↑‖x‖ : ℂ)⁻¹ • x‖ := rfl
        _ = ‖(↑‖x‖ : ℂ)⁻¹‖ * ‖x‖ := by rw [norm_smul]
        _ = ‖x‖⁻¹ * ‖x‖ := by
          rw [norm_inv]
          simp
        _ = 1 := inv_mul_cancel₀ hxnorm_ne_real
    have hy_sphere : y ∈ Metric.sphere (0 : n → ℂ) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa using hy_norm
    have hunit_y := hunit y hy_sphere
    have hAy_norm : ‖A *ᵥ y‖ = ‖A *ᵥ x‖ / ‖x‖ := by
      calc
        ‖A *ᵥ y‖ = ‖A *ᵥ ((↑‖x‖ : ℂ)⁻¹ • x)‖ := rfl
        _ = ‖(↑‖x‖ : ℂ)⁻¹ • (A *ᵥ x)‖ := by rw [Matrix.mulVec_smul]
        _ = ‖A *ᵥ x‖ / ‖x‖ := by
          rw [norm_smul, norm_inv]
          simp
          field_simp [hxnorm_ne_real]
    have hscale : ‖A *ᵥ y‖ ^ 2 * ‖x‖ ^ 2 = ‖A *ᵥ x‖ ^ 2 := by
      rw [hAy_norm]
      field_simp [hxnorm_ne_real]
    have hmul := mul_le_mul_of_nonneg_right hunit_y (sq_nonneg ‖x‖)
    rwa [hscale] at hmul

/-- A uniform entrywise bound gives a homogeneous `mulVec` norm bound for a
fixed finite matrix. This is the elementary row-sum route to an upper frame
bound. -/
lemma mulVec_norm_le_card_width_mul_entry_bound
    {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i j, ‖M i j‖ ≤ C) :
    ∀ x : n → ℂ, ‖M *ᵥ x‖ ≤ (Fintype.card n : ℝ) * C * ‖x‖ := by
  intro x
  have hD : 0 ≤ (Fintype.card n : ℝ) * C * ‖x‖ := by positivity
  refine pi_norm_le_of_forall_norm_le (M *ᵥ x) hD ?_
  intro i
  calc
    ‖(M *ᵥ x) i‖ = ‖∑ j : n, M i j * x j‖ := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j : n, ‖M i j * x j‖ := by
      simpa using norm_sum_le Finset.univ (fun j : n => M i j * x j)
    _ ≤ ∑ _j : n, C * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        ‖M i j * x j‖ = ‖M i j‖ * ‖x j‖ := norm_mul _ _
        _ ≤ C * ‖x‖ :=
          mul_le_mul (hbound i j) (pi_norm_apply_le_norm x j) (norm_nonneg _) hC
    _ = (Fintype.card n : ℝ) * C * ‖x‖ := by
      simp [mul_assoc]

/-- Squared-norm version of `mulVec_norm_le_card_width_mul_entry_bound`. -/
lemma mulVec_norm_sq_le_card_width_sq_mul_entry_bound
    {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i j, ‖M i j‖ ≤ C) :
    ∀ x : n → ℂ,
      ‖M *ᵥ x‖ ^ 2 ≤ (((Fintype.card n : ℝ) * C) ^ 2) * ‖x‖ ^ 2 := by
  intro x
  have hnorm := mulVec_norm_le_card_width_mul_entry_bound M hC hbound x
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖M *ᵥ x‖ ^ 2 ≤ ((Fintype.card n : ℝ) * C * ‖x‖) ^ 2 := hsquare
    _ = (((Fintype.card n : ℝ) * C) ^ 2) * ‖x‖ ^ 2 := by ring

/-- A uniform entrywise bound on a matrix field gives a uniform homogeneous
squared-norm upper bound for all fibers. -/
lemma uniform_mulVec_norm_sq_upper_bound_of_entry_bound
    {Ω m n : Type*} [Fintype m] [Fintype n]
    (M : Ω → Matrix m n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z i j, ‖M z i j‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z x,
      ‖M z *ᵥ x‖ ^ 2 ≤ B * ‖x‖ ^ 2 := by
  refine ⟨((Fintype.card n : ℝ) * C) ^ 2, sq_nonneg _, ?_⟩
  intro z x
  exact mulVec_norm_sq_le_card_width_sq_mul_entry_bound (M z) hC (hbound z) x

/-- A.e. strong measurability of a finite vector field gives a.e. strong
measurability of every coordinate. -/
lemma vector_components_aestronglyMeasurable
    {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (v : Ω → n → ℂ)
    (hv : AEStronglyMeasurable v μ) :
    ∀ j, AEStronglyMeasurable (fun z => v z j) μ := by
  intro j
  exact (continuous_apply j).comp_aestronglyMeasurable hv

/-- Componentwise a.e. strong measurability of a finite matrix field and vector
field implies a.e. strong measurability of their matrix-vector product. -/
lemma matrix_mulVec_aestronglyMeasurable_of_components
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
    {μ : Measure Ω}
    (M : Ω → Matrix m n ℂ) (v : Ω → n → ℂ)
    (hM : ∀ i j, AEStronglyMeasurable (fun z => M z i j) μ)
    (hv : ∀ j, AEStronglyMeasurable (fun z => v z j) μ) :
    AEStronglyMeasurable (fun z => M z *ᵥ v z) μ := by
  have hcoord : ∀ i, AEStronglyMeasurable (fun z => (M z *ᵥ v z) i) μ := by
    intro i
    have hs : AEStronglyMeasurable (∑ j : n, fun z => M z i j * v z j) μ := by
      exact Finset.aestronglyMeasurable_sum (s := Finset.univ)
        (f := fun j z => M z i j * v z j)
        (fun j _hj => (hM i j).mul (hv j))
    refine hs.congr ?_
    exact Filter.Eventually.of_forall fun z => by
      simp [Matrix.mulVec, dotProduct]
  exact (aemeasurable_pi_lambda _ fun i => (hcoord i).aemeasurable).aestronglyMeasurable

end RankCriterion

end Zak
