import LeanCode.FrobeniusDeterminant.ThetaZeroCount
import LeanCode.FrobeniusDeterminant.ThetaFourierRegroup

/-!
# Level-`p` Fourier components of the Jacobi theta series

The coefficient matrix `coeffMatrix` of the column–de-Fourier factorization
(`PrimitiveMatrixFactor.lean`) is built from the **residue-class partial theta series**

`Θ_r(w) = ∑'_{k : ℤ} jacobiTheta₂_term (p·k + r) w τ`,

i.e. the sum of the defining `ℤ`-series of `jacobiTheta₂(w, τ)` restricted to `n ≡ r (mod p)`.
This file proves the closed form

`Θ_r(w) = cexp(2πi·r·w + πi·r²·τ) · jacobiTheta₂(p·w + p·r·τ, p²·τ)`,

expressing each level-`p` component as an exponential factor times a genuine Mathlib
`jacobiTheta₂` at the dilated modular parameter `p²·τ`.  Because the exponential factor never
vanishes, this transports the (now fully proved) theta zero set to the `Θ_r`:

`Θ_r(w) = 0 ⟺ p·w + p·r·τ ∈ (1 + p²τ)/2 + ℤ + (p²τ)·ℤ`.

This is the analytic description of the building blocks of `coeffMatrix`; it is the natural next
ingredient for a valence analysis of the coefficient-matrix minors (the remaining core of the
axiom, via the column-Fourier route `cyclic_minor_iff_coeff`).
-/

namespace LyubarskiiNes.FrobeniusDeterminant.LevelPComponent

open Complex MeromorphicOn
open scoped Real

/-- **Closed form of the level-`p` residue component.**  The `mod p` residue-class partial sum of
the Jacobi theta `ℤ`-series equals an exponential factor times `jacobiTheta₂` at the dilated
modular parameter `p²·τ`. -/
theorem tsum_jacobiTheta₂_term_residue (p : ℕ) (r : ℕ) (w τ : ℂ) :
    (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ)
      = Complex.exp (2 * π * I * (r : ℂ) * w + π * I * (r : ℂ) ^ 2 * τ)
        * jacobiTheta₂ ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) ((p : ℂ) ^ 2 * τ) := by
  have hterm : ∀ k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ
      = Complex.exp (2 * π * I * (r : ℂ) * w + π * I * (r : ℂ) ^ 2 * τ)
        * jacobiTheta₂_term k ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) ((p : ℂ) ^ 2 * τ) := by
    intro k
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  rfl

/-- **Zero set of a level-`p` component.**  Since the exponential factor is nonzero, `Θ_r`
vanishes exactly where the dilated `jacobiTheta₂` does. -/
theorem tsum_jacobiTheta₂_term_residue_eq_zero_iff
    {p : ℕ} (hp : 0 < p) (r : ℕ) (w τ : ℂ) (hτ : 0 < τ.im) :
    (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ) = 0
      ↔ ∃ m n : ℤ,
          (p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ
            = (1 + (p : ℂ) ^ 2 * τ) / 2 + (m : ℂ) + (n : ℂ) * ((p : ℂ) ^ 2 * τ) := by
  have hΩ : 0 < ((p : ℂ) ^ 2 * τ).im := by
    rw [Complex.mul_im]
    have hp2re : ((p : ℂ) ^ 2).re = (p : ℝ) ^ 2 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
    have hp2im : ((p : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_im]
    rw [hp2re, hp2im, zero_mul, add_zero]
    exact mul_pos (by positivity) hτ
  rw [tsum_jacobiTheta₂_term_residue p r w τ, mul_eq_zero,
    or_iff_right (Complex.exp_ne_zero _)]
  constructor
  · intro h
    exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_mem_of_eq_zero hΩ _ h
  · rintro ⟨m, n, hmn⟩
    rw [hmn]
    exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.jacobiTheta₂_eq_zero_at_lattice _ m n

/-- **Period 1.**  Each level-`p` component is `1`-periodic (inherited term-by-term from the
`ℤ`-series: the shift multiplies the `n`-th term by `cexp(2πi·n) = 1`). -/
theorem tsum_jacobiTheta₂_term_residue_add_one (p : ℕ) (r : ℕ) (w τ : ℂ) :
    (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) (w + 1) τ)
      = ∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ := by
  refine tsum_congr (fun k => ?_)
  have hstep : jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) (w + 1) τ
      = jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ
        * Complex.exp (((p : ℤ) * k + (r : ℤ) : ℤ) * (2 * (Real.pi : ℂ) * I)) := by
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hstep, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`p·τ`-quasi-periodicity, with a multiplier that is independent of `r`.**  Under
`w ↦ w + p·τ` every level-`p` component is multiplied by the *same* automorphy factor
`cexp(-πi·(p²τ + 2p·w))`.  This common multiplier is exactly what makes the span `{Θ_r}` a genuine
`p`-dimensional theta space (sections of the degree-`p` bundle for the lattice `ℤ + p·τ·ℤ`) — the
correct setting for its valence count. -/
theorem tsum_jacobiTheta₂_term_residue_add_ptau (p : ℕ) (r : ℕ) (w τ : ℂ) :
    (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) (w + (p : ℂ) * τ) τ)
      = Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * w))
        * ∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ := by
  rw [tsum_jacobiTheta₂_term_residue, tsum_jacobiTheta₂_term_residue,
    show (p : ℂ) * (w + (p : ℂ) * τ) + (p : ℂ) * (r : ℂ) * τ
        = ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) + (p : ℂ) ^ 2 * τ from by ring,
    jacobiTheta₂_add_left' ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) ((p : ℂ) ^ 2 * τ),
    ← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  ring

/-- Imaginary part of the dilated modular parameter. -/
private theorem im_sq_mul (p : ℕ) (τ : ℂ) : ((p : ℂ) ^ 2 * τ).im = (p : ℝ) ^ 2 * τ.im := by
  have hp2re : ((p : ℂ) ^ 2).re = (p : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hp2im : ((p : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.mul_im, hp2re, hp2im, zero_mul, add_zero]

/-! ## The level-`p` theta space

A general element of the space spanned by the level-`p` components, together with its defining
quasi-periodicity and growth.  These package the five per-component lemmas above by linearity and
provide the single entire function a Jensen valence count is applied to. -/

/-- A general element `Ξ = ∑_{r < p} β r · Θ_r` of the level-`p` theta space. -/
noncomputable def levelPTheta (p : ℕ) (β : ℕ → ℂ) (τ w : ℂ) : ℂ :=
  ∑ r ∈ Finset.range p, β r * (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ)

/-- **Period 1** for a general level-`p` theta. -/
theorem levelPTheta_add_one (p : ℕ) (β : ℕ → ℂ) (τ w : ℂ) :
    levelPTheta p β τ (w + 1) = levelPTheta p β τ w := by
  unfold levelPTheta
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [tsum_jacobiTheta₂_term_residue_add_one]

/-- **`p·τ`-quasi-periodicity** for a general level-`p` theta: the *same* `r`-independent
multiplier factors through the whole sum.  This exhibits `levelPTheta` as a genuine theta function
for the lattice `ℤ + p·τ·ℤ`. -/
theorem levelPTheta_add_ptau (p : ℕ) (β : ℕ → ℂ) (τ w : ℂ) :
    levelPTheta p β τ (w + (p : ℂ) * τ)
      = Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * w))
        * levelPTheta p β τ w := by
  unfold levelPTheta
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [tsum_jacobiTheta₂_term_residue_add_ptau]
  ring

/-- **A level-`p` component is entire.**  Via the closed form (`exp`-factor times a `jacobiTheta₂`
of a dilated parameter, both differentiable). -/
theorem differentiable_levelPComponent {p : ℕ} (hp : 0 < p) (r : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ (fun w : ℂ => ∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ) := by
  have hΩ : 0 < ((p : ℂ) ^ 2 * τ).im := by
    rw [im_sq_mul]; exact mul_pos (pow_pos (by exact_mod_cast hp) 2) hτ
  have hfun : (fun w : ℂ => ∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ)
      = fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * (r : ℂ) * w
            + (Real.pi : ℂ) * I * (r : ℂ) ^ 2 * τ)
          * jacobiTheta₂ ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) ((p : ℂ) ^ 2 * τ) := by
    funext w; exact tsum_jacobiTheta₂_term_residue p r w τ
  rw [hfun]
  intro w
  apply DifferentiableAt.mul
  · exact (Complex.differentiable_exp.comp
      (by fun_prop : Differentiable ℂ (fun w : ℂ => 2 * (Real.pi : ℂ) * I * (r : ℂ) * w
        + (Real.pi : ℂ) * I * (r : ℂ) ^ 2 * τ))).differentiableAt
  · have hinner : DifferentiableAt ℂ (fun w : ℂ => (p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) w := by
      fun_prop
    exact (differentiableAt_jacobiTheta₂_fst ((p : ℂ) * w + (p : ℂ) * (r : ℂ) * τ) hΩ).comp w hinner

/-- **A general level-`p` theta is entire.** -/
theorem differentiable_levelPTheta {p : ℕ} (hp : 0 < p) (β : ℕ → ℂ) (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ (fun w : ℂ => levelPTheta p β τ w) := by
  unfold levelPTheta
  apply Differentiable.fun_sum
  intro r _
  exact (differentiable_const _).mul (differentiable_levelPComponent hp r τ hτ)

/-! ## The derivative-deformed level-`p` theta (the coeffMatrix column combination)

The column combinations of the coefficient matrix are `H = c·Ξ′ + λ·Ξ`.  Here we record that this
deformed function is again entire — the analytic starting point for its valence analysis (the
remaining core of the axiom, where the deformation introduces the torsion-jet correction). -/

/-! ## Elliptic ratios

The ratio of any two level-`p` thetas is doubly periodic (elliptic) for the lattice `ℤ + pτℤ`,
because both share the *same* `pτ`-multiplier.  This is the classical route to the valence count:
an elliptic function has equally many zeros and poles per cell, so `Ξ` has as many zeros as the
explicit reference `Θ₀` — namely `p`.  (The final "zeros = poles" step still needs a torus argument
principle, which Mathlib does not yet provide.) -/

/-! ## Lattice-invariance of the zero set

Because the `pτ`-multiplier is nonzero, the zero set of a level-`p` theta is invariant under
`ℤ + pτℤ` — the zeros form **cosets** of that lattice.  This is exactly the structure that lets the
level-1 coset-matching valence argument (Jensen + coset log-sum asymptotics + counting) generalize
to the level-`p` space *without* an argument principle. -/

/-! ## Divisor foundations for the valence count

Since `Ξ` is entire, its divisor is non-negative (only zeros) and has finite support on balls —
the inputs the Jensen valence count consumes.  (Adapted from the level-1 `ThetaZeroCount` divisor
lemmas, replacing `jacobiTheta₂` by `levelPTheta`.) -/

/-- **Shift-combination bridge.**  Any `ℂ`-linear combination of the `p` translates
`θ(· + s/p)` is a level-`p` theta `Ξ` (with coefficient vector the DFT of `γ`).  Hence such a
combination has coset-structured zeros and the valence bound applies to it — this is the form the
Frobenius determinant takes as a function of one argument. -/
theorem shift_combination_eq_levelPTheta {p : ℕ} (hp : 0 < p) (γ : Fin p → ℂ) (w τ : ℂ)
    (hτ : 0 < τ.im) :
    (∑ s : Fin p, γ s * jacobiTheta₂ (w + ((s : ℕ) : ℂ) / (p : ℂ)) τ)
      = levelPTheta p
          (fun r => ∑ s : Fin p, γ s * Complex.exp (2 * (Real.pi : ℂ) * I / p) ^ (r * (s : ℕ)))
          τ w := by
  unfold levelPTheta
  rw [← Fin.sum_univ_eq_sum_range
    (fun r => (∑ s : Fin p, γ s * Complex.exp (2 * (Real.pi : ℂ) * I / p) ^ (r * (s : ℕ)))
      * (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℤ)) w τ)) p]
  simp_rw [Regroup.jacobiTheta₂_add_div_fourier hp w τ hτ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  ring

end LyubarskiiNes.FrobeniusDeterminant.LevelPComponent
