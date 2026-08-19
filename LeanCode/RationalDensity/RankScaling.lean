import LeanCode.RationalDensity.GaussianZak
import LeanCode.FrobeniusDeterminant.PrimitiveDerivative

namespace LyubarskiiNes.RationalDensity

/-- Entrywise row/column scaling of a transposed square matrix is the
corresponding diagonal-matrix product. -/
lemma matrix_eq_scaled_transpose_of_apply
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A B : Matrix ι ι K) (rowScale colScale : ι → K)
    (h : ∀ i j, B i j = rowScale i * A j i * colScale j) :
    B = Matrix.diagonal rowScale * A.transpose * Matrix.diagonal colScale := by
  ext i j
  simp [Matrix.mul_apply, Matrix.diagonal_apply, h i j]

/-- A square matrix obtained from a transpose by nonzero diagonal row and
column scalings has nonzero determinant whenever the original matrix does. -/
lemma det_ne_zero_of_scaled_transpose
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A B : Matrix ι ι K) (rowScale colScale : ι → K)
    (hrow : ∀ i, rowScale i ≠ 0) (hcol : ∀ i, colScale i ≠ 0)
    (hB : B = Matrix.diagonal rowScale * A.transpose * Matrix.diagonal colScale)
    (hA : A.det ≠ 0) :
    B.det ≠ 0 := by
  rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (by
    intro i _hi
    exact hrow i)) hA) (Finset.prod_ne_zero_iff.mpr (by
      intro i _hi
      exact hcol i))

end LyubarskiiNes.RationalDensity
