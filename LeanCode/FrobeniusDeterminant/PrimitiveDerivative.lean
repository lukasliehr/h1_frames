import LeanCode.FrobeniusDeterminant.FrobeniusDeterminant
import LeanCode.TorsionJets.ExpConjugation
import LeanCode.ThetaFunctions.Tp
import Mathlib.LinearAlgebra.Matrix.Rank

namespace LyubarskiiNes.FrobeniusDeterminant

open Matrix

/-- The paper-side primitive theta-derivative evaluation matrix. Rows are the
torsion sample points and columns are the shifted theta basis vectors. -/
noncomputable def primitiveThetaDerivativeMatrix
    (p q : ℕ) [NeZero q] (τ lam a : ℂ) :
    Matrix (Fin q) (Fin p) ℂ :=
  fun t s =>
    LyubarskiiNes.TorsionJets.scaledDeriv
      (LyubarskiiNes.ThetaFunctions.thetaShift p τ s)
      (a + ((t : ℕ) : ℂ) / (q : ℂ)) +
    lam * LyubarskiiNes.ThetaFunctions.thetaShift p τ s
      (a + ((t : ℕ) : ℂ) / (q : ℂ))

/-- The normalized derivative of a shifted theta basis vector is the
corresponding Mathlib `jacobiTheta₂'` term times the paper derivative scale. -/
lemma scaledDeriv_thetaShift
    (p : ℕ) (τ : ℂ) (hτ : 0 < τ.im) (s : Fin p) (z : ℂ) :
    LyubarskiiNes.TorsionJets.scaledDeriv (LyubarskiiNes.ThetaFunctions.thetaShift p τ s) z =
      LyubarskiiNes.TorsionJets.paperDerivScale *
        jacobiTheta₂' (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ := by
  unfold LyubarskiiNes.TorsionJets.scaledDeriv LyubarskiiNes.ThetaFunctions.thetaShift
  have harg :
      HasDerivAt (fun w : ℂ => w + ((s : ℕ) : ℂ) / (p : ℂ)) 1 z := by
    simpa using (hasDerivAt_id z).add_const (((s : ℕ) : ℂ) / (p : ℂ))
  have hcomp := (LyubarskiiNes.ThetaFunctions.hasDerivAt_theta τ
    (z + ((s : ℕ) : ℂ) / (p : ℂ)) hτ).comp z harg
  have hderiv :
      deriv (fun w : ℂ =>
        LyubarskiiNes.ThetaFunctions.theta τ (w + ((s : ℕ) : ℂ) / (p : ℂ))) z =
        jacobiTheta₂' (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ := by
    change deriv ((fun w : ℂ => LyubarskiiNes.ThetaFunctions.theta τ w) ∘
        fun w : ℂ => w + ((s : ℕ) : ℂ) / (p : ℂ)) z = _
    simpa using hcomp.deriv
  rw [hderiv]

/-- If a matrix has rank below its number of columns, every maximal square
submatrix obtained by selecting rows has zero determinant. This is the finite
linear-algebra shell used for the rank-drop step in the primitive derivative
argument. -/
lemma det_submatrix_eq_zero_of_rank_lt
    {K rows cols : Type*} [Field K] [Fintype cols] [DecidableEq cols]
    (A : Matrix rows cols K) (row : cols → rows)
    (hA : A.rank < Fintype.card cols) :
    (A.submatrix row id).det = 0 := by
  classical
  by_contra hdet
  have hsub_rank_lt : (A.submatrix row (id : cols → cols)).rank < Fintype.card cols :=
    lt_of_le_of_lt (Matrix.rank_submatrix_le A row (id : cols → cols)) hA
  have hcols : LinearIndependent K (A.submatrix row (id : cols → cols)).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hsub_rank_eq :
      (A.submatrix row (id : cols → cols)).rank = Fintype.card cols := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact finrank_span_eq_card hcols
  exact (ne_of_lt hsub_rank_lt) hsub_rank_eq

/-- `Fin q`/`Fin p` specialization for the paper's `q × p` derivative
matrix: rank `< p` forces each selected `p × p` minor to vanish. -/
lemma fin_maximal_minor_eq_zero_of_rank_lt
    {K : Type*} [Field K] {p q : ℕ}
    (A : Matrix (Fin q) (Fin p) K) (row : Fin p → Fin q)
    (hA : A.rank < p) :
    (A.submatrix row id).det = 0 := by
  classical
  apply det_submatrix_eq_zero_of_rank_lt A row
  simpa using hA

/-- The cyclic row selector for the paper's consecutive `p × p` minors:
starting at row `j`, take rows `j, j+1, ..., j+p-1` modulo `q`. -/
def cyclicConsecutiveRows (p q : ℕ) [NeZero q] (j : Fin q) : Fin p → Fin q :=
  fun r => ⟨(j.1 + r.1) % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩

/- **Axiom eliminated.**  The former `axiom primitiveThetaDerivativeMatrix_cyclic_minor_nonzero`
(at least one cyclic consecutive torsion-evaluation minor is nonzero) is now a proved theorem
`LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix_cyclic_minor_nonzero'` in
`PrimitiveDerivativeSkeleton` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), and
its only consumer (`RationalDensity.rationalZakPMatrixH1_cyclic_minor_nonzero`) has been redirected to it. -/

/-- Rank `< p` kills the cyclic consecutive minor used in the primitive
derivative proof. This is the finite row-selection package for the minors
`M_j` after reducing row indices modulo `q`. -/
lemma fin_cyclic_consecutive_minor_eq_zero_of_rank_lt
    {K : Type*} [Field K] {p q : ℕ} [NeZero q]
    (A : Matrix (Fin q) (Fin p) K) (j : Fin q)
    (hA : A.rank < p) :
    (A.submatrix (cyclicConsecutiveRows p q j) id).det = 0 := by
  exact fin_maximal_minor_eq_zero_of_rank_lt A (cyclicConsecutiveRows p q j) hA

/-- A nonzero cyclic consecutive minor witnesses that the derivative matrix has
full column rank. This is the contrapositive form needed when the primitive
derivative proof turns a rank-drop assumption into vanished consecutive
minors. -/
lemma rank_ge_of_fin_cyclic_consecutive_minor_ne_zero
    {K : Type*} [Field K] {p q : ℕ} [NeZero q]
    (A : Matrix (Fin q) (Fin p) K) (j : Fin q)
    (hdet : (A.submatrix (cyclicConsecutiveRows p q j) id).det ≠ 0) :
    p ≤ A.rank := by
  exact le_of_not_gt fun hA =>
    hdet (fin_cyclic_consecutive_minor_eq_zero_of_rank_lt A j hA)

/-- A nonzero cyclic consecutive minor gives the full-column-rank equality
needed by the downstream scaling and frame criteria. -/
lemma rank_eq_of_fin_cyclic_consecutive_minor_ne_zero
    {K : Type*} [Field K] {p q : ℕ} [NeZero q]
    (A : Matrix (Fin q) (Fin p) K) (j : Fin q)
    (hdet : (A.submatrix (cyclicConsecutiveRows p q j) id).det ≠ 0) :
    A.rank = p := by
  exact le_antisymm
    (by simpa using Matrix.rank_le_card_width A)
    (rank_ge_of_fin_cyclic_consecutive_minor_ne_zero A j hdet)

end LyubarskiiNes.FrobeniusDeterminant
