import LeanCode.RationalDensity.RationalPositive

namespace LyubarskiiNes.MainTheorem

/-- The separable positive rational-density theorem: the Gabor system
`G(h₁, α, β)` is a frame of `L²(ℝ)` when `α·β = p/q` in lowest terms with
`q ≥ p + 2`.  The arbitrary-lattice extension is stated in
`GeneralLattice.GeneralTheorem`. -/
theorem lyubarskiiNes
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    LyubarskiiNes.IsGaborFrame α β :=
  LyubarskiiNes.RationalDensity.rational_positive hα hβ hpq_coprime hgap hαβ

end LyubarskiiNes.MainTheorem
