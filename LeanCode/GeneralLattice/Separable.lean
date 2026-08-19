import LeanCode.GeneralLattice.Definitions
import LeanCode.MainTheorem

namespace LyubarskiiNes.GeneralLattice

/-- The existing separable positive theorem, restated through the new
matrix-lattice frame predicate. -/
theorem separable_positive
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    IsGaborFrameForLattice (separableLatticeMatrix α β) := by
  rw [isGaborFrameForLattice_separable_iff]
  exact LyubarskiiNes.MainTheorem.lyubarskiiNes
    hα hβ hpq_coprime hgap hαβ

/-- The canonical rectangular representative of density `q / p`. -/
noncomputable def canonicalLatticeMatrix (p q : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  separableLatticeMatrix ((p : ℝ) / (q : ℝ)) 1

/-- The current formalization proves the positive theorem for the canonical
rectangular representative.  This is the base case to which metaplectic
covariance will reduce an arbitrary lattice. -/
theorem canonical_positive
    {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) :
    IsGaborFrameForLattice (canonicalLatticeMatrix p q) := by
  apply separable_positive (p := p) (q := q)
  · positivity
  · norm_num
  · exact hpq_coprime
  · exact hgap
  · simp [canonicalLatticeMatrix]

@[simp] lemma det_canonicalLatticeMatrix {p q : ℕ} :
    (canonicalLatticeMatrix p q).det = (p : ℝ) / (q : ℝ) := by
  simp [canonicalLatticeMatrix]

end LyubarskiiNes.GeneralLattice
