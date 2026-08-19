import LeanCode.GeneralLattice.GeneralizedWindow

open scoped BigOperators

namespace LyubarskiiNes.GeneralLattice

/-- Theta modulus obtained by sampling a generalized Gaussian on a lattice of
period `γ`. -/
noncomputable def generalizedZakTau (γ : ℝ) (τ : ℂ) : ℂ :=
  τ * (γ : ℂ) ^ 2

/-- Theta argument in the direct Zak-series expansion of `generalizedH1`. -/
noncomputable def generalizedZakArg (γ : ℝ) (τ : ℂ) (x ω : ℝ) : ℂ :=
  (γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ)

/-- Closed theta form of the Zak transform of a generalized first-Hermite
Gaussian. -/
noncomputable def generalizedZakH1ClosedForm
    (γ : ℝ) (τ : ℂ) (x ω : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
    ((x : ℂ) * jacobiTheta₂ (generalizedZakArg γ τ x ω) (generalizedZakTau γ τ) -
      (γ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        jacobiTheta₂' (generalizedZakArg γ τ x ω) (generalizedZakTau γ τ))

lemma generalizedZakTau_im_pos
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) :
    0 < (generalizedZakTau γ τ).im := by
  unfold generalizedZakTau
  have hcast : (γ : ℂ) ^ 2 = ((γ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  simpa using mul_pos hτ (sq_pos_of_ne_zero hγ)

private lemma generalizedZak_term_eq
    (γ : ℝ) (τ : ℂ) (x ω : ℝ) (k : ℤ) :
    generalizedH1 τ (x - γ * (k : ℝ)) *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (k : ℂ) * (ω : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
        ((x : ℂ) *
            jacobiTheta₂_term k (generalizedZakArg γ τ x ω) (generalizedZakTau γ τ) -
          (γ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            jacobiTheta₂'_term k
              (generalizedZakArg γ τ x ω) (generalizedZakTau γ τ)) := by
  unfold generalizedH1 generalizedZakArg generalizedZakTau
  have htwoPiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [jacobiTheta₂'_term]
  have hbracket :
      (x : ℂ) * jacobiTheta₂_term k
          ((γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ)) (τ * (γ : ℂ) ^ 2) -
        (γ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
            jacobiTheta₂_term k
              ((γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ))
              (τ * (γ : ℂ) ^ 2)) =
      ((x : ℂ) - (γ : ℂ) * (k : ℂ)) *
        jacobiTheta₂_term k
          ((γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ))
          (τ * (γ : ℂ) ^ 2) := by
    field_simp [htwoPiI]
  rw [hbracket]
  unfold jacobiTheta₂_term
  have hexp :
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ *
            ((x : ℂ) - (γ : ℂ) * (k : ℂ)) ^ 2) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (k : ℂ) * (ω : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
                ((γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ)) +
              (Real.pi : ℂ) * Complex.I * (k : ℂ) ^ 2 *
                (τ * (γ : ℂ) ^ 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [mul_assoc, hexp]
  ring

/-- Direct Zak-series formula for the metaplectic orbit of the first Hermite
window.  Unlike the old Gaussian/Poisson specialization, its theta modulus is
an arbitrary upper-half-plane parameter. -/
theorem generalizedZakH1_formula
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) (x ω : ℝ) :
    Zak.zakTransform γ (generalizedH1 τ) x ω =
      generalizedZakH1ClosedForm γ τ x ω := by
  have hΤ : 0 < (generalizedZakTau γ τ).im :=
    generalizedZakTau_im_pos hγ hτ
  have htheta :=
    (hasSum_jacobiTheta₂_term (generalizedZakArg γ τ x ω) hΤ).summable
  have htheta' :=
    (hasSum_jacobiTheta₂'_term (generalizedZakArg γ τ x ω) hΤ).summable
  unfold Zak.zakTransform generalizedZakH1ClosedForm
  rw [tsum_congr (generalizedZak_term_eq γ τ x ω)]
  rw [tsum_mul_left]
  congr 1
  rw [(htheta.mul_left (x : ℂ)).tsum_sub (htheta'.mul_left
    ((γ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹))]
  rw [tsum_mul_left, tsum_mul_left]
  rfl

/-- The theta modulus after the modular `S` transformation. -/
noncomputable def generalizedZakModularTau (γ : ℝ) (τ : ℂ) : ℂ :=
  -1 / generalizedZakTau γ τ

/-- The theta argument after the modular `S` transformation.  At rational-Zak
sample points, this has increments `-1/q` and `-1/p`. -/
noncomputable def generalizedZakModularArg
    (γ : ℝ) (τ : ℂ) (x ω : ℝ) : ℂ :=
  generalizedZakArg γ τ x ω / generalizedZakTau γ τ

/-- Modular closed form.  The bracket is exactly a normalized theta derivative
plus a scalar theta term, the operator covered by the primitive torsion-minor
theorem already present in the project. -/
noncomputable def generalizedZakH1ModularClosedForm
    (γ : ℝ) (τ : ℂ) (x ω : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
    (1 / (-Complex.I * generalizedZakTau γ τ) ^ (1 / 2 : ℂ) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (generalizedZakArg γ τ x ω) ^ 2 / generalizedZakTau γ τ)) *
    (-(γ : ℂ) / generalizedZakTau γ τ) *
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        jacobiTheta₂' (generalizedZakModularArg γ τ x ω)
          (generalizedZakModularTau γ τ) -
      (γ : ℂ) * (ω : ℂ) *
        jacobiTheta₂ (generalizedZakModularArg γ τ x ω)
          (generalizedZakModularTau γ τ))

lemma generalizedZakModularTau_im_pos
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) :
    0 < (generalizedZakModularTau γ τ).im := by
  have hT : 0 < (generalizedZakTau γ τ).im :=
    generalizedZakTau_im_pos hγ hτ
  unfold generalizedZakModularTau
  rw [Complex.div_im]
  norm_num
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hT)
    (Complex.normSq_pos.mpr (ne_of_apply_ne Complex.im (ne_of_gt hT)))

/-- Modular-transform version of `generalizedZakH1_formula`. -/
theorem generalizedZakH1_modular_formula
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) (x ω : ℝ) :
    Zak.zakTransform γ (generalizedH1 τ) x ω =
      generalizedZakH1ModularClosedForm γ τ x ω := by
  rw [generalizedZakH1_formula hγ hτ]
  unfold generalizedZakH1ClosedForm generalizedZakH1ModularClosedForm
    generalizedZakModularArg generalizedZakModularTau
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂'_functional_equation]
  let T : ℂ := generalizedZakTau γ τ
  let z : ℂ := generalizedZakArg γ τ x ω
  let C : ℂ := 1 / (-Complex.I * T) ^ (1 / 2 : ℂ)
  let E : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T)
  let dθ : ℂ := jacobiTheta₂' (z / T) (-1 / T)
  let θ : ℂ := jacobiTheta₂ (z / T) (-1 / T)
  change
    Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
        ((x : ℂ) * (C * E * θ) -
          (γ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (C * E / T * (dθ - 2 * (Real.pi : ℂ) * Complex.I * z * θ))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
        (C * E) * (-(γ : ℂ) / T) *
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * dθ -
            (γ : ℂ) * (ω : ℂ) * θ)
  have hτne : τ ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt hτ)
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hT : T = τ * (γ : ℂ) ^ 2 := rfl
  have hz : z = (γ : ℂ) * (ω : ℂ) - τ * (γ : ℂ) * (x : ℂ) := rfl
  rw [hT, hz]
  have htwoPiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [hτne, hγc, htwoPiI]
  ring

/-- Nonzero scalar prefactor in the row-operator form of the generalized Zak
transform. -/
noncomputable def generalizedZakRowPrefactor
    (γ : ℝ) (τ : ℂ) (x ω : ℝ) : ℂ :=
  (1 / (-Complex.I * generalizedZakTau γ τ) ^ (1 / 2 : ℂ)) *
    ((γ : ℂ) / generalizedZakTau γ τ) *
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (ω : ℂ) ^ 2 / τ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ))

/-- After the theta modular equation and parity, the generalized Zak transform
is a nonzero scalar times the exact normalized first-order theta operator used
by `primitiveThetaDerivativeMatrix`. -/
theorem generalizedZakH1_rowOp_formula
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) (x ω : ℝ) :
    Zak.zakTransform γ (generalizedH1 τ) x ω =
      generalizedZakRowPrefactor γ τ x ω *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            jacobiTheta₂' (-(generalizedZakModularArg γ τ x ω))
              (generalizedZakModularTau γ τ) +
          (γ : ℂ) * (ω : ℂ) *
            jacobiTheta₂ (-(generalizedZakModularArg γ τ x ω))
              (generalizedZakModularTau γ τ)) := by
  rw [generalizedZakH1_modular_formula hγ hτ]
  unfold generalizedZakH1ModularClosedForm generalizedZakRowPrefactor
  let T : ℂ := generalizedZakTau γ τ
  let z : ℂ := generalizedZakArg γ τ x ω
  let w : ℂ := generalizedZakModularArg γ τ x ω
  let Tm : ℂ := generalizedZakModularTau γ τ
  let C : ℂ := 1 / (-Complex.I * T) ^ (1 / 2 : ℂ)
  have hτne : τ ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt hτ)
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hexp :
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T) =
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (ω : ℂ) ^ 2 / τ) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) := by
    dsimp [z, T, generalizedZakArg, generalizedZakTau]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp [hτne, hγc]
    ring
  have hparity :
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * jacobiTheta₂' w Tm -
          (γ : ℂ) * (ω : ℂ) * jacobiTheta₂ w Tm =
        -((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * jacobiTheta₂' (-w) Tm +
          (γ : ℂ) * (ω : ℂ) * jacobiTheta₂ (-w) Tm) := by
    rw [jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
    ring
  change
    Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
        (C * Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T)) *
        (-(γ : ℂ) / T) *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * jacobiTheta₂' w Tm -
          (γ : ℂ) * (ω : ℂ) * jacobiTheta₂ w Tm) =
      C * ((γ : ℂ) / T) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (ω : ℂ) ^ 2 / τ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ)) *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * jacobiTheta₂' (-w) Tm +
          (γ : ℂ) * (ω : ℂ) * jacobiTheta₂ (-w) Tm)
  rw [hparity]
  rw [show
    Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
        (C * Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T)) =
      C * (Complex.exp (-(Real.pi : ℂ) * Complex.I * (ω : ℂ) ^ 2 / τ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ))) by
      calc
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
            (C * Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T)) =
          C * (Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (x : ℂ) ^ 2) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / T)) := by ring
        _ = C * (Complex.exp (-(Real.pi : ℂ) * Complex.I * (ω : ℂ) ^ 2 / τ) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (x : ℂ))) := by
          rw [hexp]]
  ring

lemma generalizedZakRowPrefactor_ne_zero
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) (x ω : ℝ) :
    generalizedZakRowPrefactor γ τ x ω ≠ 0 := by
  have hT_im : 0 < (generalizedZakTau γ τ).im := generalizedZakTau_im_pos hγ hτ
  have hT : generalizedZakTau γ τ ≠ 0 :=
    ne_of_apply_ne Complex.im (ne_of_gt hT_im)
  have hbase : -Complex.I * generalizedZakTau γ τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hT
  have hpow :
      (-Complex.I * generalizedZakTau γ τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hbase
  unfold generalizedZakRowPrefactor
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (one_div_ne_zero hpow)
        (div_ne_zero (by exact_mod_cast hγ) hT))
      (Complex.exp_ne_zero _))
    (Complex.exp_ne_zero _)

end LyubarskiiNes.GeneralLattice
