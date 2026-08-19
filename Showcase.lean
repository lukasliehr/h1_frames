import Mathlib
noncomputable section

open scoped BigOperators Real Complex InnerProductSpace Matrix
open MeasureTheory

/-! ## Mathematical notation -/

/-- The complex Hilbert space `L²(ℝ)`. -/
abbrev L2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The first Hermite function, up to a nonzero normalization constant. -/
def h1 : ℝ → ℂ := fun t =>
  (t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2)

/-- The Gabor atom `π(M(m,n))h₁`, where `M(m,n) = (x,ω)`. -/
def h1Atom (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) : ℝ → ℂ := fun t =>
  let x := M 0 0 * (m : ℝ) + M 0 1 * (n : ℝ)
  let ω := M 1 0 * (m : ℝ) + M 1 1 * (n : ℝ)
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) * h1 (t - x)

/-- Each first-Hermite Gabor atom belongs to `L²(ℝ)`. -/
lemma h1Atom_memL2 (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    MemLp (h1Atom M m n) 2 (volume : Measure ℝ) := by
  sorry

/-- The atom `π(M(m,n))h₁` as a vector in `L²(ℝ)`. -/
def h1AtomL2 (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) : L2 :=
  (h1Atom_memL2 M m n).toLp

/-- Frame condition for the Gabor system `𝒢(h₁, Mℤ²)`. -/
def IsGaborFrame (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ f : L2,
    A * ‖f‖ ^ 2 ≤
        ∑' (m : ℤ) (n : ℤ), ‖⟪f, h1AtomL2 M m n⟫_ℂ‖ ^ 2
      ∧
        ∑' (m : ℤ) (n : ℤ), ‖⟪f, h1AtomL2 M m n⟫_ℂ‖ ^ 2
          ≤ B * ‖f‖ ^ 2

/-! ## Main result -/

/-- If `Mℤ²` has density `q/p`, with `p` and `q` coprime and `q ≥ p + 2`,
then the first-Hermite Gabor system on `Mℤ²` is a frame for `L²(ℝ)`. -/
theorem MainResult
    (M : Matrix (Fin 2) (Fin 2) ℝ) {p q : ℕ}
    (hyp1 : M.det ≠ 0)
    (hyp2 : Nat.Coprime p q)
    (hyp3 : q ≥ p + 2)
    (hyp4 : |M.det|⁻¹ = (q : ℝ) / (p : ℝ)) :
    IsGaborFrame M := by
  sorry

end
