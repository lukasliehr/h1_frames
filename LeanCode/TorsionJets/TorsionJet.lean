import LeanCode.TorsionJets.ExpConjugation

namespace LyubarskiiNes.TorsionJets

/-- Bridge from the change-of-trivialization package to a standard torsion-jet
obstruction.

The hypothesis `hoperator` is the remaining concrete identification that turns
the shifted conjugated operator into the Taylor-shifted polynomial in the
standard normalized derivative. Once that identification is supplied for the
theta/residue objects, the existing nonzero/degree bookkeeping feeds directly
into the standard residue-jet contradiction `hstandard`. -/
theorem torsionJet_changeOfTrivialization_to_standardObstruction {ι : Type*}
    (A B : ℂ) {P : Polynomial ℂ} {d : WithBot ℕ}
    (g : ℂ → ℂ) (points : ι → ℂ)
    (hg : ∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g))
    (hP : P ≠ 0) (hdeg : P.degree ≤ d)
    (hoperator :
      (∀ i : ι, polynomialScaledExpConjDeriv A P g (points i) = 0) →
        ∀ i : ι,
          polynomialScaledDeriv (Polynomial.taylor (A * paperDerivScale) P) g
            (points i) = 0)
    (hstandard :
      ∀ {Q : Polynomial ℂ}, Q ≠ 0 → Q.degree ≤ d →
        (∀ i : ι, polynomialScaledDeriv Q g (points i) = 0) → False) :
    (∀ i : ι,
      polynomialScaledDeriv P ((fun z : ℂ => Complex.exp (A * z + B)) * g)
        (points i) = 0) → False := by
  intro hvanish
  rcases torsionJet_changeOfTrivialization_support
      (A := A) (B := B) (P := P) (d := d) (g := g) (points := points)
      hg hP hdeg with
    ⟨hQ_ne, hQ_degree, hvanish_iff⟩
  exact hstandard hQ_ne hQ_degree (hoperator (hvanish_iff.mp hvanish))

/-- Version of `torsionJet_changeOfTrivialization_to_standardObstruction` where
the remaining operator identification is supplied as a pointwise equality at
the torsion sample points. This is the form needed once the theta/residue
calculation identifies the shifted operator with the Taylor-shifted standard
operator. -/
theorem torsionJet_changeOfTrivialization_to_standardObstruction_of_pointwiseOperator
    {ι : Type*} (A B : ℂ) {P : Polynomial ℂ} {d : WithBot ℕ}
    (g : ℂ → ℂ) (points : ι → ℂ)
    (hg : ∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g))
    (hP : P ≠ 0) (hdeg : P.degree ≤ d)
    (hoperator_pointwise :
      ∀ i : ι,
        polynomialScaledExpConjDeriv A P g (points i) =
          polynomialScaledDeriv (Polynomial.taylor (A * paperDerivScale) P) g
            (points i))
    (hstandard :
      ∀ {Q : Polynomial ℂ}, Q ≠ 0 → Q.degree ≤ d →
        (∀ i : ι, polynomialScaledDeriv Q g (points i) = 0) → False) :
    (∀ i : ι,
      polynomialScaledDeriv P ((fun z : ℂ => Complex.exp (A * z + B)) * g)
        (points i) = 0) → False := by
  exact torsionJet_changeOfTrivialization_to_standardObstruction
    (A := A) (B := B) (P := P) (d := d) (g := g) (points := points)
    hg hP hdeg
    (by
      intro hvanish i
      simpa [hoperator_pointwise i] using hvanish i)
    hstandard

/-- Formal torsion-jet reduction currently proved: once the concrete pointwise
operator identification is available for the theta/residue objects, vanishing
after exponential change of trivialization reduces to the standard obstruction.

The remaining analytic torsion-jet work is to prove that pointwise operator
identification for the concrete functions used in the paper. -/
theorem torsion_jet_independence :
    ∀ {ι : Type*} (A B : ℂ) {P : Polynomial ℂ} {d : WithBot ℕ}
      (g : ℂ → ℂ) (points : ι → ℂ),
      (∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g)) →
      P ≠ 0 → P.degree ≤ d →
      (∀ i : ι,
        polynomialScaledExpConjDeriv A P g (points i) =
          polynomialScaledDeriv (Polynomial.taylor (A * paperDerivScale) P) g
            (points i)) →
      (∀ {Q : Polynomial ℂ}, Q ≠ 0 → Q.degree ≤ d →
        (∀ i : ι, polynomialScaledDeriv Q g (points i) = 0) → False) →
      (∀ i : ι,
        polynomialScaledDeriv P ((fun z : ℂ => Complex.exp (A * z + B)) * g)
          (points i) = 0) → False := by
  intro ι A B P d g points hg hP hdeg hoperator_pointwise hstandard hvanish
  exact torsionJet_changeOfTrivialization_to_standardObstruction_of_pointwiseOperator
    (A := A) (B := B) (P := P) (d := d) (g := g) (points := points)
    hg hP hdeg hoperator_pointwise hstandard hvanish

end LyubarskiiNes.TorsionJets
