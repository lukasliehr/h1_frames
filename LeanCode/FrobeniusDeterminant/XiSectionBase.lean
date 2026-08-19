import LeanCode.ThetaFunctions.ThetaBasic
import LeanCode.ThetaFunctions.OddTheta
import LeanCode.FrobeniusDeterminant.ThetaZeroCount

/-!
# `Ξ_p` and the theta zero set (upstream base)

This module hosts the degree-one section `Ξ_p` together with the "theta zero set"
(F2) infrastructure — the half-period vanishing, the integer/`τ`-translation laws,
the zero-set `iff`, and the odd-theta non-vanishing off the lattice.

These declarations were originally in `PrimitiveDerivativeSkeleton`, but they are
needed by *both* the skeleton and `FrobeniusFactor`.  Placing them upstream of both
breaks the former import cycle (`FrobeniusFactor` imported the skeleton solely for
`XiSection`, `theta_half_period_eq_zero`, and `oddTheta_ne_zero_of_pos_lt`), letting
the skeleton import `FrobeniusFactor`'s verified Frobenius factorization for F3.

All declarations are `sorry`-free (the only deep input, `jacobiTheta₂_mem_of_eq_zero`,
is proved in `ThetaZeroCount` via Jensen + `ZLattice` counting).
-/

namespace LyubarskiiNes.FrobeniusDeterminant

/-- The degree-one theta section `Ξ_p` from the Frobenius formula:
`θ_Ω` when `p` is odd, `ϑ_Ω` (the odd theta) when `p` is even. -/
noncomputable def XiSection (p : ℕ) (Ω : ℂ) : ℂ → ℂ :=
  if p % 2 = 1 then LyubarskiiNes.ThetaFunctions.theta Ω else LyubarskiiNes.ThetaFunctions.oddTheta Ω

/-- **Verified — half-period zero.**  `θ_Ω` vanishes at the half-period `(1+Ω)/2`. -/
theorem theta_half_period_eq_zero (Ω : ℂ) :
    LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2) = 0 := by
  have key :
      LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2)
        = - LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2) := by
    calc
      LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2)
          = LyubarskiiNes.ThetaFunctions.theta Ω ((-((1 + Ω) / 2) + Ω) + 1) := by
            congr 1; ring
      _ = LyubarskiiNes.ThetaFunctions.theta Ω (-((1 + Ω) / 2) + Ω) :=
            LyubarskiiNes.ThetaFunctions.theta_add_one_eq Ω _
      _ = Complex.exp (-↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2)))) *
            LyubarskiiNes.ThetaFunctions.theta Ω (-((1 + Ω) / 2)) :=
            LyubarskiiNes.ThetaFunctions.theta_add_tau_eq Ω (-((1 + Ω) / 2))
      _ = Complex.exp (-↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2)))) *
            LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2) := by
            rw [LyubarskiiNes.ThetaFunctions.theta_neg_eq]
      _ = (-1 : ℂ) * LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2) := by
            congr 1
            rw [show -↑Real.pi * Complex.I * (Ω + 2 * (-((1 + Ω) / 2)))
                = (↑Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
      _ = - LyubarskiiNes.ThetaFunctions.theta Ω ((1 + Ω) / 2) := by ring
  linear_combination (1 / 2 : ℂ) * key

/-- **Verified.**  `θ_Ω` is invariant under integer translation. -/
theorem theta_add_intCast (Ω z : ℂ) (m : ℤ) :
    LyubarskiiNes.ThetaFunctions.theta Ω (z + (m : ℂ)) = LyubarskiiNes.ThetaFunctions.theta Ω z := by
  have hper : Function.Periodic (fun w => LyubarskiiNes.ThetaFunctions.theta Ω w) 1 :=
    fun w => LyubarskiiNes.ThetaFunctions.theta_add_one_eq Ω w
  have h := hper.sub_int_mul_eq (x := z) (-m)
  simpa using h

/-- **Verified.**  A zero of `θ_Ω` remains a zero under integer `Ω`-translation. -/
theorem theta_eq_zero_add_intCast_mul_tau (Ω z : ℂ) (n : ℤ)
    (h : LyubarskiiNes.ThetaFunctions.theta Ω z = 0) :
    LyubarskiiNes.ThetaFunctions.theta Ω (z + (n : ℂ) * Ω) = 0 := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ k ih =>
      have e : z + (((k : ℤ) + 1 : ℤ) : ℂ) * Ω = (z + ((k : ℤ) : ℂ) * Ω) + Ω := by
        push_cast; ring
      rw [e, LyubarskiiNes.ThetaFunctions.theta_add_tau_eq, ih, mul_zero]
  | pred k ih =>
      push_cast at ih ⊢
      rw [show z + (-(k : ℂ) - 1) * Ω = (z + -(k : ℂ) * Ω) - Ω from by ring]
      have h0 := LyubarskiiNes.ThetaFunctions.theta_add_tau_eq Ω ((z + -(k : ℂ) * Ω) - Ω)
      rw [show ((z + -(k : ℂ) * Ω) - Ω) + Ω = z + -(k : ℂ) * Ω from by ring, ih] at h0
      exact (mul_eq_zero.mp h0.symm).resolve_left (Complex.exp_ne_zero _)

/-- **Verified — reverse direction of the theta zero set.** -/
theorem jacobiTheta₂_eq_zero_of_mem {Ω : ℂ} (z : ℂ) {m n : ℤ}
    (hz : z = (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω) :
    jacobiTheta₂ z Ω = 0 := by
  have hth : LyubarskiiNes.ThetaFunctions.theta Ω z = 0 := by
    rw [hz, show (1 + Ω) / 2 + (m : ℂ) + (n : ℂ) * Ω
        = ((1 + Ω) / 2 + (n : ℂ) * Ω) + (m : ℂ) from by ring, theta_add_intCast]
    exact theta_eq_zero_add_intCast_mul_tau Ω ((1 + Ω) / 2) n (theta_half_period_eq_zero Ω)
  exact hth

/-- **Verified — forward direction of the theta zero set** (wrapper to `ThetaZeroCount`). -/
theorem jacobiTheta₂_mem_of_eq_zero {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ)
    (h : jacobiTheta₂ z Ω = 0) : ∃ m n : ℤ, z = (1 + Ω) / 2 + m + n * Ω :=
  LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_mem_of_eq_zero hΩ z h

/-- **Verified.**  The theta zero set as an `iff`. -/
theorem jacobiTheta₂_eq_zero_iff_of_im_pos {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    jacobiTheta₂ z Ω = 0 ↔ ∃ m n : ℤ, z = (1 + Ω) / 2 + m + n * Ω := by
  constructor
  · intro h; exact jacobiTheta₂_mem_of_eq_zero hΩ z h
  · rintro ⟨m, n, hz⟩; exact jacobiTheta₂_eq_zero_of_mem z hz

/-- **Verified.**  The odd theta `ϑ_Ω` vanishes exactly on the lattice `ℤ + Ω·ℤ`. -/
theorem oddTheta_eq_zero_iff_of_im_pos {Ω : ℂ} (hΩ : 0 < Ω.im) (z : ℂ) :
    LyubarskiiNes.ThetaFunctions.oddTheta Ω z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + n * Ω := by
  rw [LyubarskiiNes.ThetaFunctions.oddTheta_apply, mul_eq_zero,
    or_iff_right (Complex.exp_ne_zero _)]
  show LyubarskiiNes.ThetaFunctions.theta Ω (z + (1 + Ω) / 2) = 0 ↔ _
  unfold LyubarskiiNes.ThetaFunctions.theta
  rw [jacobiTheta₂_eq_zero_iff_of_im_pos hΩ]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by linear_combination h⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by linear_combination h⟩

/-- **Verified.**  `ϑ_{pτ}(k/q) ≠ 0` for `0 < k < q`. -/
theorem oddTheta_ne_zero_of_pos_lt {p q : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (k : ℕ) (hk0 : 0 < k) (hkq : k < q) :
    LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) ((k : ℂ) / (q : ℂ)) ≠ 0 := by
  have hΩ : 0 < ((p : ℂ) * τ).im := by
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hp) hτ
  rw [Ne, oddTheta_eq_zero_iff_of_im_pos hΩ]
  rintro ⟨m, n, h⟩
  have hq0 : (q : ℂ) ≠ 0 := by
    have : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hkq
    exact_mod_cast this.ne'
  have himeq : (0 : ℝ) = (n : ℝ) * ((p : ℝ) * τ.im) := by
    have h2 := congrArg Complex.im h
    simp only [Complex.div_im, Complex.natCast_im, Complex.natCast_re, Complex.add_im,
      Complex.intCast_im, Complex.intCast_re, Complex.mul_im, Complex.mul_re,
      zero_mul, mul_zero, zero_div, zero_add, add_zero, sub_zero] at h2
    simpa [Complex.mul_im, Complex.natCast_im, Complex.natCast_re] using h2
  have hn : n = 0 := by
    have hppos : (0 : ℝ) < (p : ℝ) * τ.im := mul_pos (by exact_mod_cast hp) hτ
    have hnr : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp himeq.symm with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hppos)
    exact_mod_cast hnr
  subst hn
  simp only [Int.cast_zero, zero_mul, add_zero] at h
  rw [div_eq_iff hq0] at h
  have hkz : (k : ℤ) = m * q := by exact_mod_cast h
  have hk : (0 : ℤ) < k := by exact_mod_cast hk0
  have hkq' : (k : ℤ) < q := by exact_mod_cast hkq
  have hq : (0 : ℤ) < q := by omega
  rcases lt_or_ge 0 m with hm | hm
  · have hmq : (q : ℤ) ≤ m * (q : ℤ) := by
      calc (q : ℤ) = 1 * (q : ℤ) := (one_mul _).symm
        _ ≤ m * (q : ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hq); omega
    omega
  · have hmq : m * (q : ℤ) ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hm, le_of_lt hq⟩)
    omega

/-- **Verified — logarithmic derivative is `1`-periodic.** -/
theorem jacobiTheta₂_logDeriv_add_one (Ω z : ℂ) :
    jacobiTheta₂' (z + 1) Ω / jacobiTheta₂ (z + 1) Ω
      = jacobiTheta₂' z Ω / jacobiTheta₂ z Ω := by
  rw [jacobiTheta₂'_add_left, jacobiTheta₂_add_left]

/-- **Verified — logarithmic derivative shift under `z ↦ z + Ω`.** -/
theorem jacobiTheta₂_logDeriv_add_tau (Ω z : ℂ) (hz : jacobiTheta₂ z Ω ≠ 0) :
    jacobiTheta₂' (z + Ω) Ω / jacobiTheta₂ (z + Ω) Ω
      = jacobiTheta₂' z Ω / jacobiTheta₂ z Ω - 2 * (Real.pi : ℂ) * Complex.I := by
  rw [jacobiTheta₂'_add_left', jacobiTheta₂_add_left',
    mul_div_mul_left _ _ (Complex.exp_ne_zero _), sub_div, mul_div_assoc, div_self hz, mul_one]

end LyubarskiiNes.FrobeniusDeterminant
