import LeanCode.GeneralLattice.GeneralizedZak
import LeanCode.RationalDensity.RationalPositive.RankBounds
import LeanCode.FrobeniusDeterminant.PrimitiveDerivativeSkeleton

open scoped BigOperators Matrix

set_option maxHeartbeats 1200000

namespace LyubarskiiNes.GeneralLattice

/-- The paper-side rational Zak matrix for a generalized first-Hermite
window.  This parameterized form is used by the coefficient-fiberization
argument; on the canonical lattice `α = p/q` its Zak period is exactly `p`. -/
noncomputable def generalizedRationalZakPMatrix
    (τ : ℂ) (α : ℝ) (p q : ℕ) : ℝ × ℝ → Matrix (Fin p) (Fin q) ℂ :=
  fun z s t ↦
    Zak.zakTransform (LyubarskiiNes.RationalDensity.rationalZakGamma α q)
      (generalizedH1 τ)
      (z.1 + α * ((t : ℕ) : ℝ) +
        LyubarskiiNes.RationalDensity.rationalZakGamma α q *
          ((s : ℕ) : ℝ) / (p : ℝ)) z.2

/-- Adjoint orientation of the generalized rational Zak matrix. -/
noncomputable def generalizedRationalZakMatrix
    (τ : ℂ) (α : ℝ) (p q : ℕ) : ℝ × ℝ → Matrix (Fin q) (Fin p) ℂ :=
  fun z ↦ (generalizedRationalZakPMatrix τ α p q z)ᴴ

/-- The rational Zak matrix for a generalized first-Hermite window on the
canonical lattice `(p/q)ℤ × ℤ`, written with the period `p` used by the
existing coefficient-fiberization proof. -/
noncomputable def generalizedCanonicalZakPMatrix
    (τ : ℂ) (p q : ℕ) : ℝ × ℝ → Matrix (Fin p) (Fin q) ℂ :=
  fun z s t =>
    Zak.zakTransform (p : ℝ) (generalizedH1 τ)
      (z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ)) z.2

/-- The adjoint orientation used for lower and upper matrix bounds. -/
noncomputable def generalizedCanonicalZakMatrix
    (τ : ℂ) (p q : ℕ) : ℝ × ℝ → Matrix (Fin q) (Fin p) ℂ :=
  fun z => (generalizedCanonicalZakPMatrix τ p q z)ᴴ

lemma generalizedRationalZakPMatrix_eq_canonical
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (τ : ℂ) :
    generalizedRationalZakPMatrix τ ((p : ℝ) / (q : ℝ)) p q =
      generalizedCanonicalZakPMatrix τ p q := by
  funext z s t
  unfold generalizedRationalZakPMatrix generalizedCanonicalZakPMatrix
    LyubarskiiNes.RationalDensity.rationalZakGamma
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  congr 2 <;> field_simp [hpR, hqR]

lemma generalizedRationalZakMatrix_eq_canonical
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (τ : ℂ) :
    generalizedRationalZakMatrix τ ((p : ℝ) / (q : ℝ)) p q =
      generalizedCanonicalZakMatrix τ p q := by
  funext z
  unfold generalizedRationalZakMatrix generalizedCanonicalZakMatrix
  rw [generalizedRationalZakPMatrix_eq_canonical hp hq]

/-- Base point of the primitive theta-derivative matrix produced by the
modular Zak formula. -/
noncomputable def generalizedCanonicalPrimitiveBase
    (τ : ℂ) (p : ℕ) (z : ℝ × ℝ) : ℂ :=
  -(generalizedZakModularArg (p : ℝ) τ z.1 z.2)

lemma neg_generalizedZakModularArg_canonical_sample
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im)
    (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    -(generalizedZakModularArg (p : ℝ) τ
        (z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ)) z.2) =
      generalizedCanonicalPrimitiveBase τ p z +
        ((t : ℕ) : ℂ) / (q : ℂ) + ((s : ℕ) : ℂ) / (p : ℂ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hτne : τ ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt hτ)
  unfold generalizedCanonicalPrimitiveBase generalizedZakModularArg
    generalizedZakArg generalizedZakTau
  push_cast
  field_simp [hpR, hqR, hpC, hqC, hτne]
  ring

/-- The scalar prefactor at a rational Zak sample separates into one row
factor and one column factor. -/
lemma generalizedZakRowPrefactor_canonical_sample
    (p q : ℕ) (τ : ℂ) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    generalizedZakRowPrefactor (p : ℝ) τ
        (z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ)) z.2 =
      (generalizedZakRowPrefactor (p : ℝ) τ z.1 z.2 *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) * ((s : ℕ) : ℂ))) *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) *
            ((p : ℂ) * ((t : ℕ) : ℂ) / (q : ℂ))) := by
  unfold generalizedZakRowPrefactor
  have hexp :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) *
            ((z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ) : ℝ) : ℂ)) =
        (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) * (z.1 : ℂ)) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) * ((s : ℕ) : ℂ))) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) *
              ((p : ℂ) * ((t : ℕ) : ℂ) / (q : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Entrywise identification of the generalized rational Zak matrix with the
already-verified primitive theta-derivative matrix, up to separated nonzero
row and column scalars. -/
theorem generalizedCanonicalZakPMatrix_eq_scaled_primitive
    {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im)
    (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    generalizedCanonicalZakPMatrix τ p q z s t =
      (generalizedZakRowPrefactor (p : ℝ) τ z.1 z.2 *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) * ((s : ℕ) : ℂ))) *
      LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix p q
        (generalizedZakModularTau (p : ℝ) τ)
        ((p : ℂ) * (z.2 : ℂ))
        (generalizedCanonicalPrimitiveBase τ p z) t s *
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) *
          ((p : ℂ) * ((t : ℕ) : ℂ) / (q : ℂ))) := by
  unfold generalizedCanonicalZakPMatrix
  rw [generalizedZakH1_rowOp_formula (by exact_mod_cast Nat.ne_of_gt hp) hτ]
  rw [neg_generalizedZakModularArg_canonical_sample hp hq hτ z s t]
  rw [generalizedZakRowPrefactor_canonical_sample p q τ z s t]
  have hTm : 0 < (generalizedZakModularTau (p : ℝ) τ).im :=
    generalizedZakModularTau_im_pos (by exact_mod_cast Nat.ne_of_gt hp) hτ
  unfold LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix
  rw [LyubarskiiNes.FrobeniusDeterminant.scaledDeriv_thetaShift p _ hTm]
  unfold LyubarskiiNes.ThetaFunctions.thetaShift LyubarskiiNes.ThetaFunctions.theta
    LyubarskiiNes.TorsionJets.paperDerivScale
  norm_num
  ring_nf <;> ring

/-- Every generalized canonical rational Zak matrix has a nonzero maximal
cyclic minor in the positive range `q ≥ p + 2`. -/
theorem generalizedCanonicalZakPMatrix_cyclic_minor_nonzero
    {p q : ℕ} [NeZero q]
    (hp : 0 < p)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ z : ℝ × ℝ, ∃ j : Fin q,
      ((generalizedCanonicalZakPMatrix τ p q z).submatrix id
        (LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j)).det ≠ 0 := by
  intro z
  have hq : 0 < q := by omega
  let Tm : ℂ := generalizedZakModularTau (p : ℝ) τ
  let lam : ℂ := (p : ℂ) * (z.2 : ℂ)
  let a : ℂ := generalizedCanonicalPrimitiveBase τ p z
  rcases
      LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix_cyclic_minor_nonzero
        (p := p) (q := q) hp hpq_coprime hgap Tm a lam
          (generalizedZakModularTau_im_pos (by exact_mod_cast Nat.ne_of_gt hp) hτ) with
    ⟨j, hdet⟩
  refine ⟨j, ?_⟩
  let rows := LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j
  let A : Matrix (Fin p) (Fin p) ℂ :=
    (LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix p q Tm lam a).submatrix
      rows id
  let B : Matrix (Fin p) (Fin p) ℂ :=
    (generalizedCanonicalZakPMatrix τ p q z).submatrix id rows
  let rowScale : Fin p → ℂ := fun s =>
    generalizedZakRowPrefactor (p : ℝ) τ z.1 z.2 *
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) * ((s : ℕ) : ℂ))
  let colScale : Fin p → ℂ := fun r =>
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (z.2 : ℂ) *
        ((p : ℂ) * (((rows r : Fin q) : ℕ) : ℂ) / (q : ℂ)))
  have hentry : ∀ s r, B s r = rowScale s * A r s * colScale r := by
    intro s r
    dsimp [B, A, rowScale, colScale, rows, Tm, lam, a]
    exact generalizedCanonicalZakPMatrix_eq_scaled_primitive hp hq hτ z s _
  have hB : B = Matrix.diagonal rowScale * A.transpose * Matrix.diagonal colScale :=
    LyubarskiiNes.RationalDensity.matrix_eq_scaled_transpose_of_apply
      A B rowScale colScale hentry
  have hrow : ∀ s, rowScale s ≠ 0 := by
    intro s
    exact mul_ne_zero
      (generalizedZakRowPrefactor_ne_zero (by exact_mod_cast Nat.ne_of_gt hp) hτ _ _)
      (Complex.exp_ne_zero _)
  have hcol : ∀ r, colScale r ≠ 0 := fun r => Complex.exp_ne_zero _
  exact LyubarskiiNes.RationalDensity.det_ne_zero_of_scaled_transpose
    A B rowScale colScale hrow hcol hB hdet

/-- Full column rank of the adjoint-oriented generalized rational Zak matrix. -/
theorem generalizedCanonicalZakMatrix_injective
    {p q : ℕ} [NeZero q]
    (hp : 0 < p)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ z, Function.Injective (generalizedCanonicalZakMatrix τ p q z).mulVec := by
  intro z
  rcases generalizedCanonicalZakPMatrix_cyclic_minor_nonzero hp hpq_coprime hgap hτ z with
    ⟨j, hdet⟩
  let rows := LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j
  have hsub :
      ((generalizedCanonicalZakMatrix τ p q z).submatrix rows id) =
        ((generalizedCanonicalZakPMatrix τ p q z).submatrix id rows)ᴴ := by
    ext r s
    simp [generalizedCanonicalZakMatrix, rows]
  have hdet' :
      ((generalizedCanonicalZakMatrix τ p q z).submatrix rows id).det ≠ 0 := by
    rw [hsub, Matrix.det_conjTranspose]
    exact (star_ne_zero).2 hdet
  have hrank : (generalizedCanonicalZakMatrix τ p q z).rank = p := by
    exact LyubarskiiNes.FrobeniusDeterminant.rank_eq_of_fin_cyclic_consecutive_minor_ne_zero
      (generalizedCanonicalZakMatrix τ p q z) j hdet'
  exact (Zak.mulVec_injective_iff_rank_eq_card_width
    (generalizedCanonicalZakMatrix τ p q z)).2 (by simpa using hrank)

end LyubarskiiNes.GeneralLattice
