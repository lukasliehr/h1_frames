import LeanCode.ThetaFunctions.ThetaBasic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace LyubarskiiNes.ThetaFunctions

open scoped BigOperators

/-- Placeholder carrier for the paper's space `T_p`. -/
abbrev Tp (_p : ℕ) (_τ : ℂ) := ℂ → ℂ

/-- The paper's candidate basis vector `u_s(z) = θ_τ(z + s / p)` for `T_p`. -/
noncomputable def thetaShift (p : ℕ) (τ : ℂ) : Fin p → Tp p τ :=
  fun s z => theta τ (z + ((s : ℕ) : ℂ) / (p : ℂ))

@[simp]
theorem thetaShift_apply {p : ℕ} {τ : ℂ} (s : Fin p) (z : ℂ) :
    thetaShift p τ s z = theta τ (z + ((s : ℕ) : ℂ) / (p : ℂ)) :=
  rfl

/-- A finite Vandermonde matrix over `ℂ` is nonsingular when its nodes are
pairwise distinct. This is the determinant step needed for the DFT
change-of-basis in the eventual proof of `Tp_basis`. -/
theorem vandermonde_det_ne_zero_of_injective {n : ℕ} {v : Fin n → ℂ}
    (hv : Function.Injective v) :
    (Matrix.vandermonde v).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hji : i < j := by simpa using Finset.mem_Ioi.mp hj
  have hvne : v j ≠ v i := by
    intro h
    exact (Fin.ne_of_lt hji) (hv h.symm)
  simpa [sub_eq_zero] using hvne

/-- The Vandermonde determinant attached to distinct powers of a candidate
DFT root is nonzero. -/
theorem dft_vandermonde_det_ne_zero {p : ℕ} {ζ : ℂ}
    (hζ : Function.Injective fun s : Fin p => ζ ^ (s : ℕ)) :
    (Matrix.vandermonde fun s : Fin p => ζ ^ (s : ℕ)).det ≠ 0 :=
  vandermonde_det_ne_zero_of_injective hζ

/-- Powers of a primitive `p`th root are distinct on `Fin p`. -/
theorem dft_powers_injective_of_isPrimitiveRoot {p : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective fun s : Fin p => ζ ^ (s : ℕ) := by
  intro i j hij
  apply Fin.ext
  exact hζ.injOn_pow (by simp) (by simp) hij

/-- The DFT/Vandermonde determinant is nonzero for powers of a primitive
`p`th root of unity. -/
theorem dft_vandermonde_det_ne_zero_of_isPrimitiveRoot {p : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) :
    (Matrix.vandermonde fun s : Fin p => ζ ^ (s : ℕ)).det ≠ 0 :=
  dft_vandermonde_det_ne_zero (dft_powers_injective_of_isPrimitiveRoot hζ)

/-- The concrete finite DFT matrix with root `ζ`, indexed by exponents in
`Fin p`. -/
def dft_matrix (p : ℕ) (ζ : ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun r s => ζ ^ ((r : ℕ) * (s : ℕ))

@[simp]
theorem dft_matrix_apply {p : ℕ} {ζ : ℂ} (r s : Fin p) :
    dft_matrix p ζ r s = ζ ^ ((r : ℕ) * (s : ℕ)) :=
  rfl

/-- DFT recombination of a finite family. This is the coefficient-change
operation used to compare the elementary theta basis with the `u_s` basis. -/
def dft_recombine {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℕ) (ζ : ℂ) (u : Fin p → V) : Fin p → V :=
  fun r => ∑ s : Fin p, ζ ^ ((r : ℕ) * (s : ℕ)) • u s

@[simp]
theorem dft_recombine_apply {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {p : ℕ} {ζ : ℂ} (u : Fin p → V) (r : Fin p) :
    dft_recombine p ζ u r =
      ∑ s : Fin p, ζ ^ ((r : ℕ) * (s : ℕ)) • u s :=
  rfl

/-- The concrete DFT matrix is the Vandermonde matrix on the powers of `ζ`. -/
theorem dft_matrix_eq_vandermonde (p : ℕ) (ζ : ℂ) :
    dft_matrix p ζ = Matrix.vandermonde fun r : Fin p => ζ ^ (r : ℕ) := by
  ext r s
  simp [dft_matrix, Matrix.vandermonde, pow_mul]

/-- The determinant of the concrete DFT matrix is nonzero for a primitive root. -/
theorem dft_matrix_det_ne_zero_of_isPrimitiveRoot {p : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) :
    (dft_matrix p ζ).det ≠ 0 := by
  rw [dft_matrix_eq_vandermonde]
  exact dft_vandermonde_det_ne_zero_of_isPrimitiveRoot hζ

/-- The finite DFT recombination of the theta-shift family `u_s`. These are
the rows that are later identified with the elementary theta-space residue
basis. -/
noncomputable def dftThetaShift (p : ℕ) (ζ τ : ℂ) : Fin p → Tp p τ :=
  dft_recombine p ζ (thetaShift p τ)

@[simp]
theorem dftThetaShift_apply {p : ℕ} {ζ τ : ℂ} (r : Fin p) (z : ℂ) :
    dftThetaShift p ζ τ r z =
      ∑ s : Fin p, ζ ^ ((r : ℕ) * (s : ℕ)) *
        theta τ (z + ((s : ℕ) : ℂ) / (p : ℂ)) := by
  simp [dftThetaShift, dft_recombine, thetaShift]

end LyubarskiiNes.ThetaFunctions
