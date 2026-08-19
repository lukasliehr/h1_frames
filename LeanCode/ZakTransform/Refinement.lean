import LeanCode.ZakTransform.RankCriterion

open scoped BigOperators

namespace Zak

section RefinementReindex

variable {p : ℕ} [NeZero p]

/-- Integers indexed by a finite residue and an integer quotient. -/
noncomputable def finIntResidueEquiv (p : ℕ) [NeZero p] : Fin p × ℤ ≃ ℤ :=
  (Equiv.prodComm (Fin p) ℤ).trans (Int.divModEquiv p).symm

@[simp]
lemma finIntResidueEquiv_apply (r : Fin p) (k : ℤ) :
    finIntResidueEquiv p (r, k) = k * (p : ℤ) + (r : ℤ) := by
  simp [finIntResidueEquiv, Int.divModEquiv_symm_apply]

@[simp]
lemma finIntResidueEquiv_symm_apply (n : ℤ) :
    (finIntResidueEquiv p).symm n =
      (Fin.ofNat p (n.natMod (p : ℤ)), n / (p : ℤ)) := by
  ext <;> simp [finIntResidueEquiv, Int.divModEquiv_apply]

end RefinementReindex

end Zak
