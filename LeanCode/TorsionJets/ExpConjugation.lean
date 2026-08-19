import LeanCode.TorsionJets.FourierResidue
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Taylor

namespace LyubarskiiNes.TorsionJets

open scoped BigOperators

/-- The first-order differential operator obtained by conjugating ordinary
complex derivative by an affine exponential factor. -/
noncomputable def expConjDeriv (A : ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv g z + A * g z

/-- The scalar in the paper's normalized differential operator
`𝔡 = (2πi)⁻¹ d/dz`. -/
noncomputable abbrev paperDerivScale : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹

/-- The paper's normalized differential operator `𝔡 = (2πi)⁻¹ d/dz`. -/
noncomputable def scaledDeriv (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => paperDerivScale * deriv g z

/-- The shifted normalized derivative obtained after conjugating by
`exp (A z + B)`. -/
noncomputable def scaledExpConjDeriv (A : ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => scaledDeriv g z + (A * paperDerivScale) * g z

/-- Iterates of the normalized differential operator `𝔡`. -/
noncomputable def iterScaledDeriv : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, g => g
  | n + 1, g => scaledDeriv (iterScaledDeriv n g)

/-- Iterates of the shifted normalized derivative after exponential conjugation. -/
noncomputable def iterScaledExpConjDeriv (A : ℂ) : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, g => g
  | n + 1, g => scaledExpConjDeriv A (iterScaledExpConjDeriv A n g)

/-- Derivative of the affine exponential factor. -/
theorem hasDerivAt_exp_affine (A B z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (A * w + B))
      (Complex.exp (A * z + B) * A) z := by
  have hlin : HasDerivAt (fun w : ℂ => A * w + B) A z := by
    simpa using (((hasDerivAt_id z).const_mul A).add_const B)
  simpa using hlin.cexp

/-- Product rule for an affine exponential factor. -/
theorem hasDerivAt_exp_affine_mul {A B z : ℂ} {g : ℂ → ℂ} {gprime : ℂ}
    (hg : HasDerivAt g gprime z) :
    HasDerivAt ((fun w : ℂ => Complex.exp (A * w + B)) * g)
      (Complex.exp (A * z + B) * (gprime + A * g z)) z := by
  have h := (hasDerivAt_exp_affine A B z).mul hg
  have hderiv :
      Complex.exp (A * z + B) * A * g z + Complex.exp (A * z + B) * gprime =
        Complex.exp (A * z + B) * (gprime + A * g z) := by
    ring
  simpa [hderiv] using h

/-- First-derivative exponential-conjugation identity. -/
theorem deriv_exp_affine_mul {A B z : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g z) :
    deriv ((fun w : ℂ => Complex.exp (A * w + B)) * g) z =
      Complex.exp (A * z + B) * expConjDeriv A g z := by
  simpa [expConjDeriv] using (hasDerivAt_exp_affine_mul (A := A) (B := B)
    (z := z) (g := g) (gprime := deriv g z) hg.hasDerivAt).deriv

/-- Single-derivative exponential-conjugation identity for the paper's operator
`𝔡 = (2πi)⁻¹ d/dz`. -/
theorem scaledDeriv_exp_affine_mul {A B z : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g z) :
    scaledDeriv ((fun w : ℂ => Complex.exp (A * w + B)) * g) z =
      Complex.exp (A * z + B) * scaledExpConjDeriv A g z := by
  unfold scaledDeriv
  rw [deriv_exp_affine_mul (A := A) (B := B) (z := z) (g := g) hg]
  simp [scaledDeriv, scaledExpConjDeriv, paperDerivScale, expConjDeriv]
  ring_nf

/-- Iterated exponential-conjugation identity for the paper's normalized operator
`𝔡 = (2πi)⁻¹ d/dz`. -/
theorem iter_scaledDeriv_exp_affine_mul (A B : ℂ) (g : ℂ → ℂ)
    (hg : ∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g)) :
    ∀ n : ℕ,
      iterScaledDeriv n ((fun z : ℂ => Complex.exp (A * z + B)) * g) =
        (fun z : ℂ => Complex.exp (A * z + B)) * iterScaledExpConjDeriv A n g := by
  intro n
  induction n with
  | zero =>
      simp [iterScaledDeriv, iterScaledExpConjDeriv]
  | succ n ih =>
      simp only [iterScaledDeriv]
      rw [ih]
      funext z
      simpa [iterScaledExpConjDeriv] using
        (scaledDeriv_exp_affine_mul (A := A) (B := B) (z := z)
          (g := iterScaledExpConjDeriv A n g) ((hg n).differentiableAt))

/-- Apply a polynomial in the normalized derivative `𝔡` to a function. -/
noncomputable def polynomialScaledDeriv (P : Polynomial ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ n ∈ P.support, P.coeff n * iterScaledDeriv n g z

/-- Apply the shifted polynomial operator obtained after conjugating by
`exp (A z + B)`. -/
noncomputable def polynomialScaledExpConjDeriv (A : ℂ) (P : Polynomial ℂ)
    (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ n ∈ P.support, P.coeff n * iterScaledExpConjDeriv A n g z

/-- Polynomial version of exponential conjugation for the normalized operator
`𝔡 = (2πi)⁻¹ d/dz`. -/
theorem polynomial_scaledDeriv_exp_affine_mul
    (A B : ℂ) (P : Polynomial ℂ) (g : ℂ → ℂ)
    (hg : ∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g)) :
    polynomialScaledDeriv P ((fun z : ℂ => Complex.exp (A * z + B)) * g) =
      (fun z : ℂ => Complex.exp (A * z + B)) *
        polynomialScaledExpConjDeriv A P g := by
  funext z
  unfold polynomialScaledDeriv polynomialScaledExpConjDeriv
  calc
    (∑ n ∈ P.support,
        P.coeff n * iterScaledDeriv n ((fun z : ℂ => Complex.exp (A * z + B)) * g) z) =
        ∑ n ∈ P.support,
          P.coeff n * (Complex.exp (A * z + B) * iterScaledExpConjDeriv A n g z) := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      have hiter := congrFun (iter_scaledDeriv_exp_affine_mul A B g hg n) z
      exact congrArg (fun t => P.coeff n * t) hiter
    _ = Complex.exp (A * z + B) *
        ∑ n ∈ P.support, P.coeff n * iterScaledExpConjDeriv A n g z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n _hn
      ring

/-- The zero polynomial acts as the zero normalized differential operator. -/
@[simp]
theorem polynomialScaledDeriv_zero (g : ℂ → ℂ) :
    polynomialScaledDeriv 0 g = 0 := by
  funext z
  simp [polynomialScaledDeriv]

/-- The zero polynomial acts as the zero shifted normalized differential operator. -/
@[simp]
theorem polynomialScaledExpConjDeriv_zero (A : ℂ) (g : ℂ → ℂ) :
    polynomialScaledExpConjDeriv A 0 g = 0 := by
  funext z
  simp [polynomialScaledExpConjDeriv]

/-- A constant polynomial acts by scalar multiplication. -/
@[simp]
theorem polynomialScaledDeriv_C (c : ℂ) (g : ℂ → ℂ) :
    polynomialScaledDeriv (Polynomial.C c) g = fun z => c * g z := by
  by_cases hc : c = 0
  · subst c
    funext z
    simp [polynomialScaledDeriv]
  · funext z
    simp [polynomialScaledDeriv, Polynomial.support_C hc, iterScaledDeriv]

/-- A constant polynomial acts by scalar multiplication for the shifted operator. -/
@[simp]
theorem polynomialScaledExpConjDeriv_C (A c : ℂ) (g : ℂ → ℂ) :
    polynomialScaledExpConjDeriv A (Polynomial.C c) g = fun z => c * g z := by
  by_cases hc : c = 0
  · subst c
    funext z
    simp [polynomialScaledExpConjDeriv]
  · funext z
    simp [polynomialScaledExpConjDeriv, Polynomial.support_C hc, iterScaledExpConjDeriv]

/-- A monomial picks out the corresponding iterate of `𝔡`. -/
@[simp]
theorem polynomialScaledDeriv_monomial (n : ℕ) (c : ℂ) (g : ℂ → ℂ) :
    polynomialScaledDeriv (Polynomial.monomial n c) g =
      fun z => c * iterScaledDeriv n g z := by
  by_cases hc : c = 0
  · subst c
    funext z
    simp [polynomialScaledDeriv]
  · funext z
    simp [polynomialScaledDeriv, Polynomial.support_monomial n hc]

/-- A shifted monomial picks out the corresponding shifted iterate. -/
@[simp]
theorem polynomialScaledExpConjDeriv_monomial (A : ℂ) (n : ℕ) (c : ℂ) (g : ℂ → ℂ) :
    polynomialScaledExpConjDeriv A (Polynomial.monomial n c) g =
      fun z => c * iterScaledExpConjDeriv A n g z := by
  by_cases hc : c = 0
  · subst c
    funext z
    simp [polynomialScaledExpConjDeriv]
  · funext z
    simp [polynomialScaledExpConjDeriv, Polynomial.support_monomial n hc]

/-- Taylor translation preserves nonzero polynomials. -/
theorem polynomial_taylor_ne_zero {r : ℂ} {P : Polynomial ℂ} (hP : P ≠ 0) :
    (Polynomial.taylor r) P ≠ 0 := by
  exact fun h => hP ((Polynomial.taylor_eq_zero r P).mp h)

/-- Taylor translation preserves polynomial degree. -/
theorem polynomial_degree_taylor (r : ℂ) (P : Polynomial ℂ) :
    ((Polynomial.taylor r) P).degree = P.degree := by
  exact Polynomial.degree_taylor P r

/-- Taylor translation preserves polynomial `natDegree`. -/
theorem polynomial_natDegree_taylor (r : ℂ) (P : Polynomial ℂ) :
    ((Polynomial.taylor r) P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_taylor P r

/-- Taylor translation preserves an upper bound on polynomial degree. -/
theorem polynomial_taylor_degree_le {r : ℂ} {P : Polynomial ℂ} {d : WithBot ℕ}
    (hdeg : P.degree ≤ d) :
    ((Polynomial.taylor r) P).degree ≤ d := by
  simpa [polynomial_degree_taylor] using hdeg

/-- Change-of-trivialization support for the torsion-jet argument.

After removing the nonvanishing affine exponential factor, the polynomial that
will be fed into the standard torsion-jet contradiction is still nonzero and
has the same degree bound; vanishing of the original normalized differential
operator at any chosen family of sample points is equivalent to vanishing of
the shifted operator there. -/
theorem torsionJet_changeOfTrivialization_support {ι : Type*}
    (A B : ℂ) {P : Polynomial ℂ} {d : WithBot ℕ}
    (g : ℂ → ℂ) (points : ι → ℂ)
    (hg : ∀ n : ℕ, Differentiable ℂ (iterScaledExpConjDeriv A n g))
    (hP : P ≠ 0) (hdeg : P.degree ≤ d) :
    (Polynomial.taylor (A * paperDerivScale) P ≠ 0) ∧
      ((Polynomial.taylor (A * paperDerivScale) P).degree ≤ d) ∧
        ((∀ i : ι,
            polynomialScaledDeriv P ((fun z : ℂ => Complex.exp (A * z + B)) * g)
              (points i) = 0) ↔
          ∀ i : ι, polynomialScaledExpConjDeriv A P g (points i) = 0) := by
  refine ⟨polynomial_taylor_ne_zero hP, polynomial_taylor_degree_le hdeg, ?_⟩
  constructor
  · intro h i
    have hpoint :=
      congrFun (polynomial_scaledDeriv_exp_affine_mul A B P g hg) (points i)
    have hz :
        Complex.exp (A * points i + B) *
            polynomialScaledExpConjDeriv A P g (points i) = 0 := by
      simpa [hpoint, Pi.mul_apply] using h i
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  · intro h i
    have hpoint :=
      congrFun (polynomial_scaledDeriv_exp_affine_mul A B P g hg) (points i)
    rw [hpoint]
    simp [Pi.mul_apply, h i]

end LyubarskiiNes.TorsionJets
