import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace LyubarskiiNes.FrobeniusDeterminant

open Matrix

/-- If two distinct rows of a square matrix are scalar multiples, then the
determinant vanishes. This is the finite determinant step used in the
Frobenius diagonal-divisor argument. -/
lemma det_eq_zero_of_row_eq_smul_row
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) {i j : n} (hij : i ≠ j) (c : K)
    (hrow : ∀ k, A i k = c * A j k) :
    A.det = 0 := by
  let B : Matrix n n K := A.updateRow i (A j)
  let v : n → K := Function.update (fun _ => (1 : K)) i c
  have hji : j ≠ i := Ne.symm hij
  have hBrow : B i = B j := by
    unfold B
    rw [Matrix.updateRow_self, Matrix.updateRow_ne hji]
  have hscale : A = Matrix.of fun r k => v r * B r k := by
    ext r k
    by_cases hr : r = i
    · subst r
      simp [B, v, hrow k]
    · simp [B, v, hr]
  calc
    A.det = (Matrix.of fun r k => v r * B r k).det := by rw [hscale]
    _ = (∏ r, v r) * B.det := Matrix.det_mul_column v B
    _ = 0 := by
      rw [Matrix.det_zero_of_row_eq hij hBrow, mul_zero]

end LyubarskiiNes.FrobeniusDeterminant
