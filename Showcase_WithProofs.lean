import LeanCode.GeneralLattice.GeneralTheorem

/-!
# The Lyubarskii--Nes theorem for arbitrary lattices -- machine-checked proof

This file has the same public definitions and theorem as `Showcase.lean`, with
the two proof bodies supplied by the full formalization.
-/

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

private lemma h1Atom_eq_library
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    h1Atom M m n = LyubarskiiNes.GeneralLattice.h1LatticeElement M m n := by
  funext t
  simp [h1Atom, h1, LyubarskiiNes.GeneralLattice.h1LatticeElement,
    LyubarskiiNes.GeneralLattice.latticeTime,
    LyubarskiiNes.GeneralLattice.latticeFrequency]
  ring

/-- Each first-Hermite Gabor atom belongs to `L²(ℝ)`. -/
lemma h1Atom_memL2 (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    MemLp (h1Atom M m n) 2 (volume : Measure ℝ) := by
  rw [h1Atom_eq_library]
  exact LyubarskiiNes.GeneralLattice.memLp_h1LatticeElement M m n

/-- The atom `π(M(m,n))h₁` as a vector in `L²(ℝ)`. -/
def h1AtomL2 (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) : L2 :=
  (h1Atom_memL2 M m n).toLp

private lemma h1AtomL2_eq_library
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    h1AtomL2 M m n =
      LyubarskiiNes.GeneralLattice.h1LatticeElementLp M m n := by
  unfold h1AtomL2 LyubarskiiNes.GeneralLattice.h1LatticeElementLp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t => congrFun (h1Atom_eq_library M m n) t

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
  have hframe :=
    LyubarskiiNes.GeneralLattice.lyubarskiiNes_general_positive
      M hyp1 hyp2 hyp3 hyp4
  simpa only [IsGaborFrame,
    LyubarskiiNes.GeneralLattice.IsGaborFrameForLattice,
    h1AtomL2_eq_library] using hframe

-- Kernel audit: only Lean's standard foundational axioms are used.
#print axioms MainResult
#print axioms h1Atom_memL2

end
