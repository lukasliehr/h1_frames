import LeanCode.FrobeniusDeterminant.LevelPComponent
import LeanCode.TorsionJets.TorsionJet
import LeanCode.FrobeniusDeterminant.XiSectionBase
import LeanCode.FrobeniusDeterminant.ResidueTheorem

/-!
# Towards the Frobenius determinant factorization (F1)

The skeleton residual `frobenius_factorization` is the classical Frobenius theta-determinant
formula.  Its proof rests on the level-`p` **valence bound** (`LevelPComponent`): viewing the
determinant `det[θ(u_r + s/p)]` as a function of one argument `u₀`, it is a `ℂ`-linear combination
of the translates `θ(u₀ + s/p)` (cofactor/row-multilinearity), hence a level-`p` theta with
coset-structured zeros — so the valence bound caps its zero-cosets, which drives the factorization.

This file builds that route.  First step: the row-expansion of a determinant along one row (pure
linear algebra), and its consequence that the Frobenius determinant is a shift-combination in `u₀`.
-/

namespace LyubarskiiNes.FrobeniusDeterminant.FrobeniusFactor

open Matrix Complex
open scoped Real

/-- **Row expansion of a determinant.**  The determinant is `ℂ`-linear in any single row; expanding
that row in the standard basis gives `det(updateRow M i g) = ∑ₛ gₛ · det(updateRow M i eₛ)`. -/
theorem det_updateRow_expand {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) (g : Fin p → ℂ) :
    (M.updateRow i g).det = ∑ s : Fin p, g s * (M.updateRow i (Pi.single s 1)).det := by
  classical
  let L : (Fin p → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => (M.updateRow i v).det
      map_add' := det_updateRow_add M i
      map_smul' := fun a v => det_updateRow_smul M i a v }
  have hg : g = ∑ s : Fin p, g s • (Pi.single s 1 : Fin p → ℂ) := by
    funext t
    simp [Finset.sum_apply, Pi.single_apply]
  calc (M.updateRow i g).det
      = L g := rfl
    _ = L (∑ s : Fin p, g s • (Pi.single s 1 : Fin p → ℂ)) := by rw [← hg]
    _ = ∑ s : Fin p, g s • L (Pi.single s 1) := by rw [map_sum]; simp_rw [map_smul]
    _ = ∑ s : Fin p, g s * (M.updateRow i (Pi.single s 1)).det := by
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]

/-- **The Frobenius determinant, as a function of one row's argument `w`, is a level-`p` theta.**
Replacing row `0` by the theta-translate row `s ↦ θ(w + s/p)` and expanding along that row exhibits
the determinant as a shift-combination `∑ₛ (cofactorₛ)·θ(w + s/p)`, which is a `levelPTheta` in `w`
(with coefficient vector the DFT of the cofactors).  Hence the determinant has **coset-structured
zeros** and the valence bound `≤ p` applies to it — the analytic heart of the Frobenius
factorization. -/
theorem frobenius_det_row0_eq_levelPTheta {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (M : Matrix (Fin p) (Fin p) ℂ) (w : ℂ) :
    (M.updateRow ⟨0, hp⟩ (fun s => jacobiTheta₂ (w + ((s : ℕ) : ℂ) / (p : ℂ)) τ)).det
      = LevelPComponent.levelPTheta p
          (fun r => ∑ s : Fin p, (M.updateRow ⟨0, hp⟩ (Pi.single s 1)).det
            * Complex.exp (2 * (Real.pi : ℂ) * I / p) ^ (r * (s : ℕ))) τ w := by
  rw [det_updateRow_expand M ⟨0, hp⟩ (fun s => jacobiTheta₂ (w + ((s : ℕ) : ℂ) / (p : ℂ)) τ),
    ← LevelPComponent.shift_combination_eq_levelPTheta hp
      (fun s => (M.updateRow ⟨0, hp⟩ (Pi.single s 1)).det) w τ hτ]
  exact Finset.sum_congr rfl (fun s _ => mul_comm _ _)

/-- The Frobenius theta-matrix in explicit form, as a function of the argument vector `u`. -/
noncomputable def frobMatrix (p : ℕ) (τ : ℂ) (u : Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun r s => jacobiTheta₂ (u r + ((s : ℕ) : ℂ) / (p : ℂ)) τ

/-- **Explicit zeros of the Frobenius determinant.**  When two arguments coincide the corresponding
rows are equal, so the determinant vanishes.  Together with the coset-invariance of the zero set,
each coincidence `u_{r₁} ≡ u_{r₂}  (mod ℤ + pτℤ)` contributes a full zero-coset — the `p−1` explicit
zeros that, against the valence bound `≤ p`, pin the factorization. -/
theorem frobMatrix_det_eq_zero_of_arg_eq {p : ℕ} (τ : ℂ) (u : Fin p → ℂ)
    {r₁ r₂ : Fin p} (hr : r₁ ≠ r₂) (heq : u r₁ = u r₂) :
    (frobMatrix p τ u).det = 0 := by
  apply Matrix.det_zero_of_row_eq hr
  funext s
  simp only [frobMatrix, Matrix.of_apply, heq]

/-- Updating the argument vector at index `i` is the same as updating row `i` of the matrix. -/
theorem frobMatrix_update_eq_updateRow {p : ℕ} (τ : ℂ) (u : Fin p → ℂ) (i : Fin p) (w : ℂ) :
    frobMatrix p τ (Function.update u i w)
      = (frobMatrix p τ u).updateRow i (fun s => jacobiTheta₂ (w + ((s : ℕ) : ℂ) / (p : ℂ)) τ) := by
  ext r s
  simp only [frobMatrix, Matrix.of_apply, Matrix.updateRow_apply, Function.update_apply]
  split_ifs with h <;> rfl

/-- **The Frobenius determinant, as a function of the `i`-th argument, is a level-`p` theta.**
Combining `frobMatrix_update_eq_updateRow` with `frobenius_det_row0_eq_levelPTheta` (specialised to
row `i`): so its zeros are coset-structured and the valence bound `≤ p` applies. -/
theorem frobMatrix_det_update_eq_levelPTheta {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (w : ℂ) :
    (frobMatrix p τ (Function.update u ⟨0, hp⟩ w)).det
      = LevelPComponent.levelPTheta p
          (fun r => ∑ s : Fin p,
            ((frobMatrix p τ u).updateRow ⟨0, hp⟩ (Pi.single s 1)).det
              * Complex.exp (2 * (Real.pi : ℂ) * I / p) ^ (r * (s : ℕ))) τ w := by
  rw [frobMatrix_update_eq_updateRow, frobenius_det_row0_eq_levelPTheta hp τ hτ]

/-- **Elliptic Liouville.**  An entire function periodic for two `ℝ`-independent periods `1` and `c`
(`0 < c.im`) is constant: it equals its values on the compact fundamental cell `{s + t·c : s,t ∈
[0,1]}`, hence has bounded range, hence is constant by Liouville.  This is the degree-one
classification engine for the Frobenius factorization (`det/∏ϑ`, being elliptic and pole-free, is
constant). -/
theorem const_of_entire_doubly_periodic (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {c : ℂ} (hc : 0 < c.im) (h1 : Function.Periodic f 1) (hcp : Function.Periodic f c) :
    ∃ C : ℂ, ∀ z : ℂ, f z = C := by
  set K : Set ℂ :=
    (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 • c) '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) with hKdef
  have hKcomp : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hsurj : ∀ z : ℂ, ∃ k ∈ K, f z = f k := by
    intro z
    set b : ℝ := z.im / c.im with hb
    set a : ℝ := z.re - b * c.re with ha
    have hz : z = (a : ℂ) + b • c := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.smul_re, smul_eq_mul, ha]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, smul_eq_mul, zero_add, hb]
        field_simp
    have hmem : ((Int.fract a, Int.fract b) : ℝ × ℝ)
        ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩
        ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩
    have hkK : ((Int.fract a : ℝ) : ℂ) + (Int.fract b : ℝ) • c ∈ K :=
      hKdef ▸ ⟨(Int.fract a, Int.fract b), hmem, rfl⟩
    refine ⟨((Int.fract a : ℝ) : ℂ) + (Int.fract b : ℝ) • c, hkK, ?_⟩
    rw [hz, ← h1.sub_int_mul_eq ⌊a⌋ (x := (a : ℂ) + b • c),
      ← hcp.sub_int_mul_eq ⌊b⌋ (x := (a : ℂ) + b • c - (⌊a⌋ : ℂ) * 1)]
    congr 1
    simp only [Int.fract, Complex.real_smul]
    push_cast
    ring
  have hbound : Bornology.IsBounded (Set.range f) := by
    have hsub : Set.range f ⊆ f '' K := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨k, hk, hfk⟩ := hsurj z
      exact ⟨k, hk, hfk.symm⟩
    exact ((hKcomp.image hf.continuous).isBounded).subset hsub
  obtain ⟨C, hC⟩ := hf.exists_eq_const_of_bounded hbound
  exact ⟨C, fun z => congrFun hC z⟩

open LevelPComponent

/-- **`Ξ_p` under `z ↦ z + 1`.**  The degree-one section picks up `(-1)^{p+1}`: for odd `p` it is `θ`
(period `1`, factor `+1`); for even `p` it is the odd theta `ϑ` (`ϑ(z+1) = -ϑ(z)`, factor `-1`). -/
theorem XiSection_add_one (p : ℕ) (Ω z : ℂ) :
    XiSection p Ω (z + 1) = (-1 : ℂ) ^ (p + 1) * XiSection p Ω z := by
  unfold XiSection
  split_ifs with h
  · rw [LyubarskiiNes.ThetaFunctions.theta_add_one_eq]
    have : Even (p + 1) := (Nat.odd_iff.mpr h).add_one
    rw [this.neg_one_pow, one_mul]
  · rw [LyubarskiiNes.ThetaFunctions.oddTheta_add_one_eq]
    have : Odd (p + 1) := (Nat.even_iff.mpr (by omega)).add_one
    rw [this.neg_one_pow]; ring

/-- **Odd theta under `z ↦ z + Ω`.**  Derived from `θ`'s quasi-periodicity: `ϑ_Ω(z+Ω) =
e^{-πi(Ω+2z+1)} ϑ_Ω(z)` — the same `θ`-multiplier `e^{-πi(Ω+2z)}` times the antiperiodic sign `-1`. -/
theorem oddTheta_add_tau_eq (Ω z : ℂ) :
    LyubarskiiNes.ThetaFunctions.oddTheta Ω (z + Ω)
      = Complex.exp (-(Real.pi : ℂ) * I * (Ω + 2 * z + 1)) * LyubarskiiNes.ThetaFunctions.oddTheta Ω z := by
  simp only [LyubarskiiNes.ThetaFunctions.oddTheta_apply]
  rw [show z + Ω + (1 + Ω) / 2 = (z + (1 + Ω) / 2) + Ω by ring, LyubarskiiNes.ThetaFunctions.theta_add_tau_eq,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

/-- `ϑ_Ω(z-Ω) = e^{πi(2z-Ω+1)} ϑ_Ω(z)` (inverse of `oddTheta_add_tau_eq`). -/
theorem oddTheta_sub_tau (Ω z : ℂ) :
    LyubarskiiNes.ThetaFunctions.oddTheta Ω (z - Ω)
      = Complex.exp ((Real.pi : ℂ) * I * (2 * z - Ω + 1)) * LyubarskiiNes.ThetaFunctions.oddTheta Ω z := by
  have h := oddTheta_add_tau_eq Ω (z - Ω)
  rw [show z - Ω + Ω = z by ring] at h
  rw [h, ← mul_assoc, ← Complex.exp_add,
    show (Real.pi : ℂ) * I * (2 * z - Ω + 1) + -(Real.pi : ℂ) * I * (Ω + 2 * (z - Ω) + 1) = 0 by ring,
    Complex.exp_zero, one_mul]

/-- **`Ξ_p` under `z ↦ z + Ω`.**  The degree-one section's `Ω`-multiplier: `Ξ_p(z+Ω) =
(-1)^{p+1} e^{-πi(Ω+2z)} Ξ_p(z)` (θ-multiplier for odd `p`, odd-theta multiplier for even `p`). -/
theorem XiSection_add_tau (p : ℕ) (Ω z : ℂ) :
    XiSection p Ω (z + Ω)
      = (-1 : ℂ) ^ (p + 1) * Complex.exp (-(Real.pi : ℂ) * I * (Ω + 2 * z)) * XiSection p Ω z := by
  unfold XiSection
  split_ifs with h
  · rw [LyubarskiiNes.ThetaFunctions.theta_add_tau_eq]
    have : Even (p + 1) := (Nat.odd_iff.mpr h).add_one
    rw [this.neg_one_pow]; ring
  · rw [oddTheta_add_tau_eq]
    have : Odd (p + 1) := (Nat.even_iff.mpr (by omega)).add_one
    rw [this.neg_one_pow,
      show -(Real.pi : ℂ) * I * (Ω + 2 * z + 1)
        = (-(Real.pi : ℂ) * I * (Ω + 2 * z)) + (-((Real.pi : ℂ) * I)) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring

/-- `ϑ_Ω(z-1) = -ϑ_Ω(z)` (rearranged antiperiodicity). -/
theorem oddTheta_sub_one (Ω z : ℂ) :
    LyubarskiiNes.ThetaFunctions.oddTheta Ω (z - 1) = -LyubarskiiNes.ThetaFunctions.oddTheta Ω z := by
  have h := LyubarskiiNes.ThetaFunctions.oddTheta_add_one_eq Ω (z - 1)
  rw [show z - 1 + 1 = z by ring] at h
  linear_combination h

/-- **The Frobenius comparison function** in the `0`-th argument `w`: the degree-one section `Ξ_p`
at the shifted sum times the theta-Vandermonde factors that involve index `0`.  The Frobenius
factorization (F1) asserts the determinant, as a function of `w = u₀`, is a constant multiple of this. -/
noncomputable def frobComparison (p : ℕ) (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (w : ℂ) : ℂ :=
  XiSection p ((p : ℂ) * τ) (w + ∑ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p), u s)
    * ∏ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
        LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w)

/-- **The comparison function has period `1`** — matching the level-`p` determinant.  The `Ξ_p`
factor contributes `(-1)^{p+1}` and the `p-1` antiperiodic `ϑ` factors contribute `(-1)^{p-1}`; their
product is `(-1)^{2p} = 1`. -/
theorem frobComparison_add_one (p : ℕ) (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (w : ℂ) :
    frobComparison p hp τ u (w + 1) = frobComparison p hp τ u w := by
  unfold frobComparison
  set E := Finset.univ.erase (⟨0, hp⟩ : Fin p) with hE
  rw [show w + 1 + ∑ s ∈ E, u s = (w + ∑ s ∈ E, u s) + 1 by ring, XiSection_add_one]
  have hstep : ∀ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - (w + 1))
      = (-1) * LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w) := by
    intro s _
    rw [show u s - (w + 1) = (u s - w) - 1 by ring, oddTheta_sub_one]; ring
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : E.card = p - 1 := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  have hsign : (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ (p - 1) = 1 := by
    rw [← pow_add, show (p + 1) + (p - 1) = 2 * p by omega, pow_mul]; norm_num
  rw [show (-1 : ℂ) ^ (p + 1) * XiSection p ((p : ℂ) * τ) (w + ∑ s ∈ E, u s)
        * ((-1 : ℂ) ^ (p - 1) * ∏ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w))
      = ((-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ (p - 1))
        * (XiSection p ((p : ℂ) * τ) (w + ∑ s ∈ E, u s)
          * ∏ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w)) by ring,
    hsign, one_mul]

/-- **The comparison function has the level-`p` `pτ`-multiplier** `e^{-πi(p²τ+2pw)}` — exactly the
multiplier of the determinant section (`levelPTheta_add_ptau`).  The `Ξ_p` factor and the `p-1`
`ϑ`-factors each contribute a `pτ`-multiplier; their product, after the sign `(-1)^{2p}=1` and the
`e^{2pπi}=1` reduction, collapses to the level-`p` multiplier.  Together with `frobComparison_add_one`
this makes the ratio `det / cmp` an **elliptic function** for `ℤ + pτℤ`. -/
theorem frobComparison_add_ptau (p : ℕ) (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (w : ℂ) :
    frobComparison p hp τ u (w + (p : ℂ) * τ)
      = Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * w))
        * frobComparison p hp τ u w := by
  unfold frobComparison
  set E := Finset.univ.erase (⟨0, hp⟩ : Fin p) with hE
  have hcardN : E.card = p - 1 := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hcard : (E.card : ℂ) = (p : ℂ) - 1 := by rw [hcardN, Nat.cast_pred hp]
  set S := ∑ s ∈ E, u s with hS
  rw [show w + (p : ℂ) * τ + S = (w + S) + (p : ℂ) * τ by ring, XiSection_add_tau]
  have hstep : ∀ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - (w + (p : ℂ) * τ))
      = Complex.exp ((Real.pi : ℂ) * I * (2 * (u s - w) - (p : ℂ) * τ + 1))
        * LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w) := by
    intro s _
    rw [show u s - (w + (p : ℂ) * τ) = (u s - w) - (p : ℂ) * τ by ring, oddTheta_sub_tau]
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hsum : ∑ s ∈ E, ((Real.pi : ℂ) * I * (2 * (u s - w) - (p : ℂ) * τ + 1))
      = (Real.pi : ℂ) * I * (2 * S - (E.card : ℂ) * (2 * w + (p : ℂ) * τ - 1)) := by
    rw [← Finset.mul_sum]; congr 1
    have hh : ∀ s, 2 * (u s - w) - (p : ℂ) * τ + 1 = 2 * (u s) - (2 * w + (p : ℂ) * τ - 1) :=
      fun s => by ring
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← hS]
  rw [hsum, hcard]
  have hscalar : (-1 : ℂ) ^ (p + 1)
      * (Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) * τ + 2 * (w + S)))
        * Complex.exp ((Real.pi : ℂ) * I * (2 * S - ((p : ℂ) - 1) * (2 * w + (p : ℂ) * τ - 1))))
      = Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * w)) := by
    have hsign : (-1 : ℂ) ^ (p + 1) = Complex.exp (((p : ℂ) + 1) * ((Real.pi : ℂ) * I)) := by
      rw [← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hsign, ← Complex.exp_add, ← Complex.exp_add,
      show ((p : ℂ) + 1) * ((Real.pi : ℂ) * I)
          + (-(Real.pi : ℂ) * I * ((p : ℂ) * τ + 2 * (w + S))
            + (Real.pi : ℂ) * I * (2 * S - ((p : ℂ) - 1) * (2 * w + (p : ℂ) * τ - 1)))
        = -(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * w)
          + (p : ℂ) * (2 * (Real.pi : ℂ) * I) by ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]
  rw [show ((-1 : ℂ) ^ (p + 1)
        * Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) * τ + 2 * (w + S)))
        * XiSection p ((p : ℂ) * τ) (w + S))
      * (Complex.exp ((Real.pi : ℂ) * I * (2 * S - ((p : ℂ) - 1) * (2 * w + (p : ℂ) * τ - 1)))
        * ∏ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w))
      = ((-1 : ℂ) ^ (p + 1)
          * (Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) * τ + 2 * (w + S)))
            * Complex.exp ((Real.pi : ℂ) * I * (2 * S - ((p : ℂ) - 1) * (2 * w + (p : ℂ) * τ - 1)))))
        * (XiSection p ((p : ℂ) * τ) (w + S)
          * ∏ s ∈ E, LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w)) by ring,
    hscalar]

/-- The odd theta is entire (in `z`) for `Ω` in the upper half-plane. -/
theorem differentiableAt_oddTheta (Ω z : ℂ) (hΩ : 0 < Ω.im) :
    DifferentiableAt ℂ (LyubarskiiNes.ThetaFunctions.oddTheta Ω) z := by
  have haff : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) * I * Ω / 4 + (Real.pi : ℂ) * I * z) z := by fun_prop
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z + (1 + Ω) / 2) z :=
    differentiableAt_id.add_const _
  have h2 : DifferentiableAt ℂ (fun z : ℂ => LyubarskiiNes.ThetaFunctions.theta Ω (z + (1 + Ω) / 2)) z := by
    simpa [Function.comp_def] using
      (LyubarskiiNes.ThetaFunctions.differentiableAt_theta Ω (z + (1 + Ω) / 2) hΩ).comp z hshift
  unfold LyubarskiiNes.ThetaFunctions.oddTheta
  exact haff.cexp.mul h2

/-- The degree-one section `Ξ_p` is entire (in `z`) for `Ω` in the upper half-plane. -/
theorem differentiableAt_XiSection (p : ℕ) (Ω z : ℂ) (hΩ : 0 < Ω.im) :
    DifferentiableAt ℂ (XiSection p Ω) z := by
  unfold XiSection
  split_ifs
  · exact LyubarskiiNes.ThetaFunctions.differentiableAt_theta Ω z hΩ
  · exact differentiableAt_oddTheta Ω z hΩ

/-- **The comparison function is entire** (a product of the entire section `Ξ_p` and entire
`ϑ`-factors) — the numerator differentiability needed for the meromorphic ratio `det/cmp`. -/
theorem differentiable_frobComparison {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (u : Fin p → ℂ) :
    Differentiable ℂ (frobComparison p hp τ u) := by
  have hΩ : 0 < ((p : ℂ) * τ).im := by
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hp) hτ
  intro w
  unfold frobComparison
  apply DifferentiableAt.mul
  · simpa [Function.comp_def] using
      (differentiableAt_XiSection p ((p : ℂ) * τ) _ hΩ).comp w (differentiableAt_id.add_const _)
  · rw [show (fun w : ℂ => ∏ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w))
        = ∏ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
          fun w : ℂ => LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - w) by
      funext w'; rw [Finset.prod_apply]]
    refine DifferentiableAt.finsetProd fun s _ => ?_
    simpa [Function.comp_def] using
      (differentiableAt_oddTheta ((p : ℂ) * τ) _ hΩ).comp w
        ((differentiableAt_const _).sub differentiableAt_id)

/-- The odd theta vanishes at the origin (a lattice point): `ϑ_Ω(0) = 0`, since
`ϑ_Ω(0) = e^{…}·θ_Ω((1+Ω)/2)` and `θ_Ω` vanishes at the half period. -/
theorem oddTheta_zero (Ω : ℂ) : LyubarskiiNes.ThetaFunctions.oddTheta Ω 0 = 0 := by
  rw [LyubarskiiNes.ThetaFunctions.oddTheta_apply, zero_add, theta_half_period_eq_zero, mul_zero]

/-- **The comparison function shares the determinant's explicit zeros.**  `cmp` vanishes at each
argument `u s` (`s ≠ 0`): the factor `ϑ_{pτ}(u s − u s) = ϑ_{pτ}(0) = 0`.  Combined with
`levelPTheta_frobDetCoeff_zero_at` (the det-section vanishing there too), these `p-1` common zeros are
what let the ratio extend holomorphically across them. -/
theorem frobComparison_zero_at {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (s : Fin p)
    (hs : s ≠ ⟨0, hp⟩) : frobComparison p hp τ u (u s) = 0 := by
  unfold frobComparison
  apply mul_eq_zero_of_right
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩) ?_
  rw [sub_self, oddTheta_zero]

/-- The `levelPTheta` coefficient vector of the Frobenius determinant viewed as a function of its
`0`-th argument (the DFT of the row-`0` cofactors). -/
noncomputable def frobDetCoeff {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) : ℕ → ℂ :=
  fun r => ∑ s : Fin p, ((frobMatrix p τ u).updateRow ⟨0, hp⟩ (Pi.single s 1)).det
    * Complex.exp (2 * (Real.pi : ℂ) * I / p) ^ (r * (s : ℕ))

/-- **Explicit zeros of the Frobenius det-section.**  As a level-`p` theta in its `0`-th argument, the
Frobenius determinant vanishes at each of the other arguments `u s` (`s ≠ 0`): setting the `0`-th
argument to `u s` makes rows `0` and `s` coincide.  These are the `p−1` explicit zero-cosets that,
against the valence bound `≤ p`, pin the degree-one factor `Ξ_p`. -/
theorem levelPTheta_frobDetCoeff_zero_at {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (s : Fin p) (hs : s ≠ ⟨0, hp⟩) :
    levelPTheta p (frobDetCoeff hp τ u) τ (u s) = 0 := by
  have h : (frobMatrix p τ (Function.update u ⟨0, hp⟩ (u s))).det = 0 := by
    refine frobMatrix_det_eq_zero_of_arg_eq τ (Function.update u ⟨0, hp⟩ (u s)) hs ?_
    rw [Function.update_apply, Function.update_apply, if_neg hs, if_pos rfl]
  rw [← h]
  exact (frobMatrix_det_update_eq_levelPTheta hp τ hτ u (u s)).symm

/-- **`g = θ'/θ − m/(·−ζ)` (with the pole removed) is holomorphic on the cell neighbourhood.**
At the centre `ζ = (1+Ω)/2` the simple pole cancels (`differentiableAt_logDeriv_sub_extend`); elsewhere
`θ ≠ 0` (`theta_ne_zero_cellNbhd`) so it is `differentiableAt_logDeriv_sub_away`.  This is the
holomorphic integrand whose parallelogram Cauchy integral is `0`, completing `∮ θ'/θ = m·2πi`. -/
theorem differentiableOn_logDeriv_sub_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    DifferentiableOn ℂ
      (Function.update (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2))
        ((1 + Ω) / 2) (logDeriv u ((1 + Ω) / 2)))
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) := by
  intro z hz
  by_cases hzζ : z = (1 + Ω) / 2
  · subst hzζ
    exact (ResidueTheorem.differentiableAt_logDeriv_sub_extend hu hune hfac).differentiableWithinAt
  · have hθa : AnalyticAt ℂ (fun w => jacobiTheta₂ w Ω) z :=
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ z (Set.mem_univ z)
    have hθ0 : jacobiTheta₂ z Ω ≠ 0 :=
      LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_ne_zero_cellNbhd hΩ hz hzζ
    exact (ResidueTheorem.differentiableAt_logDeriv_sub_away hθa hθ0 hzζ).differentiableWithinAt

/-- The closed fundamental cell (base point `0`, sides `1` and `Ω`) lies in the open cell
neighbourhood — the containment `parContourIntegral_eq_zero_of_holo` consumes. -/
theorem cell_subset_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) (s t : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (0 : ℂ) + (s : ℂ) + (t : ℂ) * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω := by
  have hΩ0 : Ω.im ≠ 0 := ne_of_gt hΩ
  refine ⟨?_, ?_⟩
  · have h : ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).re
        - ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).im / Ω.im * Ω.re = s := by
      simp only [Complex.add_re, Complex.add_im, Complex.zero_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, zero_add, zero_mul, sub_zero, add_zero]
      field_simp; ring
    rw [h]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · have h : ((0:ℂ) + (s : ℂ) + (t : ℂ) * Ω).im / Ω.im = t := by
      simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, zero_add, zero_mul, add_zero]
      field_simp
    rw [h]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **The four sides of the `ζ`-centered cell avoid the pole `ζ = (1+Ω)/2`.**  Bottom/top by imaginary
part (`0, Ω.im ≠ Ω.im/2`); right/left by forcing `t = 1/2` from the imaginary part, then a real-part
contradiction.  This lets `g` and its removable extension agree on the contour. -/
theorem sides_ne_zeta {Ω : ℂ} (hΩ : 0 < Ω.im) (t : ℝ) :
    (0:ℂ) + (t : ℂ) ≠ (1 + Ω)/2 ∧ (0:ℂ) + Ω + (t : ℂ) ≠ (1 + Ω)/2 ∧
    (0:ℂ) + 1 + (t : ℂ) * Ω ≠ (1 + Ω)/2 ∧ (0:ℂ) + (t : ℂ) * Ω ≠ (1 + Ω)/2 := by
  have hΩ0 : Ω.im ≠ 0 := ne_of_gt hΩ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.div_im, Complex.add_im,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, Complex.add_re,
      Complex.one_re, Complex.div_re, zero_add, zero_mul, add_zero, mul_zero] at this
    nlinarith [this, hΩ]
  · intro h; have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.div_im, Complex.add_im,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, Complex.add_re,
      Complex.one_re, Complex.div_re, zero_add, add_zero, mul_zero] at this
    nlinarith [this, hΩ]
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.div_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_re, Complex.one_re, Complex.div_re, zero_add, zero_mul,
      add_zero, mul_zero] at him
    have ht : t = 1/2 := mul_right_cancel₀ hΩ0 (by nlinarith [him] : t * Ω.im = 1/2 * Ω.im)
    subst ht
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.mul_im, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_im, Complex.one_im, Complex.div_im, zero_add, zero_mul,
      add_zero, sub_zero, mul_zero] at hre
    nlinarith [hre]
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.div_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_re, Complex.one_re, Complex.div_re, zero_add, zero_mul,
      add_zero, mul_zero] at him
    have ht : t = 1/2 := mul_right_cancel₀ hΩ0 (by nlinarith [him] : t * Ω.im = 1/2 * Ω.im)
    subst ht
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.mul_im, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat, Complex.add_im, Complex.one_im, Complex.div_im, zero_add, zero_mul,
      add_zero, sub_zero, mul_zero] at hre
    nlinarith [hre]

/-- The four sides of the cell (as parametrised by `parContourIntegral`) lie in the cell
neighbourhood for `t ∈ [0,1]` — the continuity input the residue split's integrability needs. -/
theorem sides_mem_cellNbhd {Ω : ℂ} (hΩ : 0 < Ω.im) (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    (0:ℂ) + ↑t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + 1 + ↑t * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + Ω + ↑t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω ∧
    (0:ℂ) + ↑t * Ω ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h11 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((0:ℂ) + ↑t) = 0 + ↑t + ↑(0:ℝ) * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ t 0 ht h01
  · rw [show ((0:ℂ) + 1 + ↑t * Ω) = 0 + ↑(1:ℝ) + ↑t * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ 1 t h11 ht
  · rw [show ((0:ℂ) + Ω + ↑t) = 0 + ↑t + ↑(1:ℝ) * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ t 1 ht h11
  · rw [show ((0:ℂ) + ↑t * Ω) = 0 + ↑(0:ℝ) + ↑t * Ω from by push_cast; ring]
    exact cell_subset_cellNbhd hΩ 0 t h01 ht

/-- **Residue side, part 1: `∮_∂P (θ'/θ − m/(·−ζ)) = 0`.**  The integrand agrees on the contour with
its removable extension `g_ext` (they differ only at `ζ`, off the contour by `sides_ne_zeta`), and
`g_ext` is holomorphic on the whole cell, so the parallelogram Cauchy theorem gives `0`. -/
theorem theta_contour_g_zero {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    ResidueTheorem.parContourIntegral
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) 0 Ω = 0 := by
  set g : ℂ → ℂ := fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)
    with hg
  set gext := Function.update g ((1 + Ω) / 2) (logDeriv u ((1 + Ω) / 2)) with hgext
  have hgext0 : ResidueTheorem.parContourIntegral gext 0 Ω = 0 :=
    ResidueTheorem.parContourIntegral_eq_zero_of_holo _
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω)
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.isOpen_cellNbhd Ω)
      (differentiableOn_logDeriv_sub_cellNbhd hΩ hu hune hfac) 0 Ω
      (fun s t hs ht => by simpa using cell_subset_cellNbhd hΩ s t hs ht)
  have hupd : ∀ w : ℂ, w ≠ (1 + Ω) / 2 → g w = gext w :=
    fun w hw => (Function.update_of_ne hw _ g).symm
  have key : ResidueTheorem.parContourIntegral g 0 Ω = ResidueTheorem.parContourIntegral gext 0 Ω := by
    simp only [ResidueTheorem.parContourIntegral]
    rw [intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.1),
      intervalIntegral.integral_congr (fun t _ => hupd _ (sides_ne_zeta hΩ t).2.2.2)]
  rw [key, hgext0]

/-- **Periodicity side of the argument principle for `θ`.**  `∮_∂P θ'/θ = 2πi` around the fundamental
cell (base `0`, sides `1` and `Ω`): the log-derivative has period `1` (`jacobiTheta₂_logDeriv_add_one`)
and a `−2πi` jump under `+Ω` (`jacobiTheta₂_logDeriv_add_tau`, valid since `θ` has no real zeros), and
`θ'/θ` is integrable on the real bottom side (θ non-vanishing there). -/
theorem theta_logDeriv_periodicity {Ω : ℂ} (hΩ : 0 < Ω.im) :
    ResidueTheorem.parContourIntegral (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω
      = 2 * (Real.pi : ℂ) * I := by
  have hθan : AnalyticOnNhd ℂ (fun w => jacobiTheta₂ w Ω) Set.univ :=
    fun z _ => LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ z (Set.mem_univ z)
  have hθc : Continuous (fun w => jacobiTheta₂ w Ω) :=
    (analyticOnNhd_univ_iff_differentiable.mp hθan).continuous
  have hdθc : Continuous (deriv (fun w => jacobiTheta₂ w Ω)) :=
    (analyticOnNhd_univ_iff_differentiable.mp hθan.deriv).continuous
  refine ResidueTheorem.parContourIntegral_logDeriv_eq
    (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω ?_ ?_ ?_
  · intro t
    simp only [LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.logDeriv_jacobiTheta₂_eq hΩ]
    rw [show (0:ℂ) + 1 + (t:ℂ) * Ω = ((t:ℂ) * Ω) + 1 by ring,
      show (0:ℂ) + (t:ℂ) * Ω = (t:ℂ) * Ω by ring]
    exact jacobiTheta₂_logDeriv_add_one Ω ((t:ℂ) * Ω)
  · intro t
    simp only [LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.logDeriv_jacobiTheta₂_eq hΩ]
    rw [show (0:ℂ) + Ω + (t:ℂ) = (t:ℂ) + Ω by ring, show (0:ℂ) + (t:ℂ) = (t:ℂ) by ring]
    exact jacobiTheta₂_logDeriv_add_tau Ω (t:ℂ)
      (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_no_real_zero hΩ t)
  · apply ContinuousOn.intervalIntegrable
    have hcongr : (fun t : ℝ => logDeriv (fun w => jacobiTheta₂ w Ω) (0 + (t:ℂ)))
        = fun t : ℝ => deriv (fun w => jacobiTheta₂ w Ω) (0 + (t:ℂ)) / jacobiTheta₂ (0 + (t:ℂ)) Ω := by
      funext t; rw [logDeriv_apply]
    rw [hcongr]
    apply ContinuousOn.div ((hdθc.comp (by fun_prop)).continuousOn)
      ((hθc.comp (by fun_prop)).continuousOn)
    intro t _
    simp only [Function.comp_apply, zero_add]
    exact LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_no_real_zero hΩ t

/-- **Residue side of the argument principle: `∮_∂P θ'/θ = m·2πi`.**  Split `θ'/θ = m·(1/(·−ζ)) + g`,
where `g = θ'/θ − m/(·−ζ)` extends holomorphically across `ζ`.  The `g`-part integrates to `0`
(`theta_contour_g_zero`) and the pole part to `m·2πi` (winding number `parContourIntegral_inv_eq`). -/
theorem theta_contour_logDeriv_eq {Ω : ℂ} (hΩ : 0 < Ω.im) {m : ℕ} {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ((1 + Ω) / 2)) (hune : u ((1 + Ω) / 2) ≠ 0)
    (hfac : (fun z => jacobiTheta₂ z Ω) =ᶠ[nhds ((1 + Ω) / 2)]
      fun z => (z - (1 + Ω) / 2) ^ m • u z) :
    ResidueTheorem.parContourIntegral (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z) 0 Ω
      = (m : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  set gext := Function.update
    (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) ((1 + Ω) / 2)
    (logDeriv u ((1 + Ω) / 2)) with hgext
  have hgc : ContinuousOn gext (LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) :=
    (differentiableOn_logDeriv_sub_cellNbhd hΩ hu hune hfac).continuousOn
  have hupd : ∀ w : ℂ, w ≠ (1 + Ω) / 2 →
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) w = gext w := by
    intro w hw; rw [hgext]
    exact (Function.update_of_ne hw (logDeriv u ((1 + Ω) / 2))
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2))).symm
  have gInt : ∀ (S : ℝ → ℂ), Continuous S →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ∈ LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.cellNbhd Ω) →
      (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ (1 + Ω) / 2) →
      IntervalIntegrable
        (fun t => logDeriv (fun w => jacobiTheta₂ w Ω) (S t) - (m : ℂ) / ((S t) - (1 + Ω) / 2))
        MeasureTheory.volume 0 1 := by
    intro S hS hmem hne
    apply ContinuousOn.intervalIntegrable
    exact (hgc.comp hS.continuousOn hmem).congr (fun t ht => hupd (S t) (hne t ht))
  have hInt : ∀ (S : ℝ → ℂ), Continuous S → (∀ t, t ∈ Set.uIcc (0:ℝ) 1 → S t ≠ (1 + Ω) / 2) →
      IntervalIntegrable (fun t => (m : ℂ) * (1 / ((S t) - (1 + Ω) / 2))) MeasureTheory.volume 0 1 := by
    intro S hS hne
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      ((hS.sub continuous_const).continuousOn) (fun t ht => ?_))
    rw [sub_ne_zero]; exact hne t ht
  have heq : (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z)
      = fun z => (m : ℂ) * (1 / (z - (1 + Ω) / 2))
        + (logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) := by
    funext z; rw [mul_one_div]; ring
  rw [heq, ResidueTheorem.parContourIntegral_split (fun z => (m : ℂ) * (1 / (z - (1 + Ω) / 2)))
      (fun z => logDeriv (fun w => jacobiTheta₂ w Ω) z - (m : ℂ) / (z - (1 + Ω) / 2)) 0 Ω
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.1))
      (hInt _ (by fun_prop) (fun t _ => (sides_ne_zeta hΩ t).2.2.2))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).1)
        (fun t _ => (sides_ne_zeta hΩ t).1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.1)
        (fun t _ => (sides_ne_zeta hΩ t).2.2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.2.1)
        (fun t _ => (sides_ne_zeta hΩ t).2.1))
      (gInt _ (by fun_prop) (fun t ht => (sides_mem_cellNbhd hΩ t ht).2.2.2)
        (fun t _ => (sides_ne_zeta hΩ t).2.2.2))]
  rw [ResidueTheorem.parContourIntegral_const_mul, theta_contour_g_zero hΩ hu hune hfac, add_zero]
  rw [show ResidueTheorem.parContourIntegral (fun z => 1 / (z - (1 + Ω) / 2)) 0 Ω
      = 2 * (Real.pi : ℂ) * I from by
    simpa using ResidueTheorem.parContourIntegral_inv_eq ((1 + Ω) / 2) Ω hΩ]

/-- **The theta has a simple zero at `ζ = (1+Ω)/2`.**  Equating the two evaluations of the contour
integral `∮_∂P θ'/θ` — the residue side `m·2πi` and the periodicity side `2πi` — forces `m = 1`. -/
theorem theta_simple_zero {Ω : ℂ} (hΩ : 0 < Ω.im) :
    analyticOrderAt (fun w => jacobiTheta₂ w Ω) ((1 + Ω) / 2) = 1 := by
  obtain ⟨m, u, hm1, hu, hune, hfac⟩ := LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_order_factorization hΩ
  have hAt : AnalyticAt ℂ (fun w => jacobiTheta₂ w Ω) ((1 + Ω) / 2) :=
    LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hΩ _ (Set.mem_univ _)
  have hm : (m : ℂ) * (2 * (Real.pi : ℂ) * I) = 2 * (Real.pi : ℂ) * I := by
    rw [← theta_contour_logDeriv_eq hΩ hu hune hfac, theta_logDeriv_periodicity hΩ]
  have h2πne : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hmc : (m : ℂ) = 1 := mul_right_cancel₀ h2πne (by rw [one_mul]; exact hm)
  have hmeq : m = 1 := by exact_mod_cast hmc
  rw [hAt.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hune, hfac⟩, hmeq, Nat.cast_one]

/-- **F4 conjunct 2 (general form): every iterated scaled-exp-conjugated derivative of an entire
function is entire.**  Induction on `n`: each step is `𝔡(·) + A·s·(·)`, and the derivative of an entire
function is entire (analyticity of `ℂ`-differentiable functions).  Applied with `g` the standard theta
factor of `Ξ_p`, this is the differentiability conjunct of `XiSection_changeOfTrivialization_data`. -/
theorem differentiable_iterScaledExpConjDeriv (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∀ n : ℕ, Differentiable ℂ (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) := by
  intro n
  induction n with
  | zero => simpa [LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv] using hg
  | succ n ih =>
    have hd : Differentiable ℂ (deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g)) :=
      analyticOnNhd_univ_iff_differentiable.mp
        (analyticOnNhd_univ_iff_differentiable.mpr ih).deriv
    have heq : LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A (n + 1) g
        = fun z => LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) z
          + (A * LyubarskiiNes.TorsionJets.paperDerivScale)
            * LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g z := by
      funext z; rfl
    rw [heq]
    exact (differentiable_const _ |>.mul hd).add ((differentiable_const _).mul ih)

/-- Every iterate of the plain normalized derivative `𝔡` of an entire function is entire. -/
theorem diff_iterScaledDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) := by
  induction k with
  | zero => exact hg
  | succ k ihk =>
    have hd : Differentiable ℂ (deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g)) :=
      analyticOnNhd_univ_iff_differentiable.mp (analyticOnNhd_univ_iff_differentiable.mpr ihk).deriv
    have heq : LyubarskiiNes.TorsionJets.iterScaledDeriv (k + 1) g
        = fun z => LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z := rfl
    rw [heq]; exact (differentiable_const _).mul hd

/-- The derivative of a finite `𝔡`-iterate combination distributes over the sum. -/
theorem deriv_sum_iterScaledDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    deriv (fun w => ∑ k ∈ Finset.range N, c k * LyubarskiiNes.TorsionJets.iterScaledDeriv k g w) z
      = ∑ k ∈ Finset.range N, c k * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z := by
  rw [deriv_fun_sum]
  · exact Finset.sum_congr rfl (fun k _ => by
      rw [deriv_const_mul _ ((diff_iterScaledDeriv hg k).differentiableAt)])
  · exact fun k _ => ((differentiable_const (c k)).mul (diff_iterScaledDeriv hg k)).differentiableAt

/-- Weighted Pascal recurrence used for the operator binomial theorem. -/
theorem weighted_pascal (F : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k : ℂ) * x^(n-k) * F (k+1))
    + (∑ k ∈ Finset.range (n+1), (n.choose k : ℂ) * x^(n+1-k) * F k)
    = ∑ k ∈ Finset.range (n+2), ((n+1).choose k : ℂ) * x^(n+1-k) * F k := by
  rw [Finset.sum_range_succ' (fun k => ((n+1).choose k : ℂ) * x^(n+1-k) * F k) (n+1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, pow_succ]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℂ) * x^(n+1-k) * F k) n]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.succ_sub_succ,
    Finset.sum_add_distrib, add_mul]
  rw [Finset.sum_range_succ (fun k => (n.choose (k+1) : ℂ) * x^(n-k) * F (k+1)) n, Nat.choose_succ_self]
  push_cast; ring

/-- **Operator binomial theorem.**  Because `𝔡` and the constant `A·s` commute, the exp-conjugated
iterate expands binomially: `(𝔡 + A·s)ⁿ g = ∑ₖ C(n,k)(A·s)^{n−k} 𝔡ᵏ g`.  This is the algebraic heart
of the Taylor-shift operator identity (F4 conjunct 3). -/
theorem iterScaledExpConjDeriv_binomial (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) :
    LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g
      = fun z => ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * (A * LyubarskiiNes.TorsionJets.paperDerivScale) ^ (n - k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z := by
  induction n with
  | zero => funext z; simp [LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv, LyubarskiiNes.TorsionJets.iterScaledDeriv]
  | succ n ih =>
    funext z
    have hstep : LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A (n + 1) g z
        = LyubarskiiNes.TorsionJets.paperDerivScale
            * deriv (LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g) z
          + (A * LyubarskiiNes.TorsionJets.paperDerivScale)
            * LyubarskiiNes.TorsionJets.iterScaledExpConjDeriv A n g z := rfl
    rw [hstep, ih, deriv_sum_iterScaledDeriv hg (n+1)
        (fun k => (n.choose k : ℂ) * (A * LyubarskiiNes.TorsionJets.paperDerivScale) ^ (n - k)) z,
        Finset.mul_sum, Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (n+1), LyubarskiiNes.TorsionJets.paperDerivScale
          * ((n.choose k : ℂ) * (A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z))
        = ∑ k ∈ Finset.range (n+1), (n.choose k : ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) g z from
      Finset.sum_congr rfl (fun k _ => by
        show _ = _ * _ * (LyubarskiiNes.TorsionJets.paperDerivScale
          * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k g) z); ring)]
    rw [show (∑ k ∈ Finset.range (n+1), (A*LyubarskiiNes.TorsionJets.paperDerivScale)
          * ((n.choose k:ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z))
        = ∑ k ∈ Finset.range (n+1), (n.choose k:ℂ)*(A*LyubarskiiNes.TorsionJets.paperDerivScale)^(n+1-k)
            * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z from
      Finset.sum_congr rfl (fun k hk => by
        have hkn : n - k + 1 = n + 1 - k := by rw [Finset.mem_range] at hk; omega
        rw [← hkn, pow_succ]; ring)]
    exact weighted_pascal (fun k => LyubarskiiNes.TorsionJets.iterScaledDeriv k g z)
      (A * LyubarskiiNes.TorsionJets.paperDerivScale) n

open Polynomial LyubarskiiNes.TorsionJets in
/-- **F4 conjunct 3: the Taylor-shift operator identity.**  Applying the polynomial `P` in the
exp-conjugated derivative `𝔡 + A·s` equals applying the Taylor-shifted polynomial `taylor (A·s) P` in
the plain derivative `𝔡`.  Both sides are linear in `P`; on monomials the identity is the operator
binomial theorem (`iterScaledExpConjDeriv_binomial`) matched against the Taylor coefficient of a
monomial (`hasseDeriv_monomial`).  This is the "remaining concrete identification" that
`torsion_jet_independence` consumes for `XiSection_changeOfTrivialization_data`. -/
theorem polynomialScaledExpConjDeriv_eq_taylor (A : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (P : Polynomial ℂ) :
    polynomialScaledExpConjDeriv A P g
      = polynomialScaledDeriv (taylor (A * paperDerivScale) P) g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    funext z
    have hL : polynomialScaledExpConjDeriv A (p + q) g z
        = polynomialScaledExpConjDeriv A p g z + polynomialScaledExpConjDeriv A q g z := by
      show (p + q).sum (fun n c => c * iterScaledExpConjDeriv A n g z) = _
      rw [Polynomial.sum_add_index]
      · rfl
      · intro n; ring
      · intro n a b; ring
    have hR : polynomialScaledDeriv (taylor (A * paperDerivScale) (p + q)) g z
        = polynomialScaledDeriv (taylor (A * paperDerivScale) p) g z
          + polynomialScaledDeriv (taylor (A * paperDerivScale) q) g z := by
      rw [map_add]
      show (taylor (A * paperDerivScale) p + taylor (A * paperDerivScale) q).sum
          (fun n c => c * iterScaledDeriv n g z) = _
      rw [Polynomial.sum_add_index]
      · rfl
      · intro n; ring
      · intro n a b; ring
    rw [hL, hR, congrFun hp z, congrFun hq z]
  | monomial n a =>
    funext z
    simp only [polynomialScaledExpConjDeriv_monomial]
    rw [congrFun (iterScaledExpConjDeriv_binomial A hg n) z, Finset.mul_sum]
    have hR : polynomialScaledDeriv (taylor (A * paperDerivScale) (monomial n a)) g z
        = ∑ k ∈ Finset.range (n+1),
            (n.choose k : ℂ) * a * (A * paperDerivScale)^(n-k) * iterScaledDeriv k g z := by
      show (taylor (A * paperDerivScale) (monomial n a)).sum
          (fun m c => c * iterScaledDeriv m g z) = _
      rw [Polynomial.sum_over_range' _ (fun m => by ring) (n+1) (by
        rw [polynomial_natDegree_taylor]
        exact Nat.lt_succ_of_le (Polynomial.natDegree_monomial_le a))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show (taylor (A * paperDerivScale) (monomial n a)).coeff k
          = (n.choose k : ℂ) * a * (A * paperDerivScale)^(n-k) from by
        rw [taylor_coeff, hasseDeriv_monomial, eval_monomial]]
    rw [hR]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The normalized operator `𝔡` commutes with multiplication by a constant. -/
theorem iterScaledDeriv_const_mul (C : ℂ) (f : ℂ → ℂ) (k : ℕ) :
    LyubarskiiNes.TorsionJets.iterScaledDeriv k (fun z => C * f z)
      = fun z => C * LyubarskiiNes.TorsionJets.iterScaledDeriv k f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    have h1 : LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) (fun z => C * f z) z
        = LyubarskiiNes.TorsionJets.paperDerivScale
          * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k (fun z => C * f z)) z := rfl
    have h2 : LyubarskiiNes.TorsionJets.iterScaledDeriv (k+1) f z
        = LyubarskiiNes.TorsionJets.paperDerivScale * deriv (LyubarskiiNes.TorsionJets.iterScaledDeriv k f) z := rfl
    rw [h1, ih, h2, deriv_const_mul_field]; ring

/-- **`mᵏ`-weighted summability of the theta terms** — the tail bound `|m|ᵏ·e^{−π(Tm²−2S|m|)}` is
summable (`summable_pow_mul_jacobiTheta₂_term_bound`), so the `mᵏ`-weighted theta series converges. -/
theorem summable_intpow_theta_term {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) (k : ℕ) :
    Summable (fun n : ℤ => (n:ℂ)^k * jacobiTheta₂_term n z τ) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ k).of_norm_bounded ?_
  intro n; rw [norm_mul, norm_pow, Complex.norm_intCast, ← Int.cast_abs]; gcongr
  exact norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n

/-- **Finite character orthogonality:** for a frequency `m` not divisible by `q`,
`Σ_{s<q} e^{2πim·s/q} = 0` (geometric sum with primitive `q`-th root of unity). -/
theorem exp_orthogonality {q : ℕ} (hq : 0 < q) (m : ℤ) (hm : ¬ (q:ℤ) ∣ m) :
    ∑ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*((s:ℕ)/(q:ℂ))) = 0 := by
  have hq0 : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have h2πi : (2*(Real.pi:ℂ)*I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hpow : ∀ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*((s:ℕ)/(q:ℂ)))
      = (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^(s:ℕ) := by
    intro s; rw [← Complex.exp_nat_mul]; congr 1; field_simp
  rw [Finset.sum_congr rfl (fun s _ => hpow s), Fin.sum_univ_eq_sum_range
    (fun s => (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^s) q]
  rw [geom_sum_eq]
  · have hωq : (Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)))^q = 1 := by
      rw [← Complex.exp_nat_mul,
        show (q:ℂ)*(2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) = (m:ℂ)*(2*(Real.pi:ℂ)*I) from by field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hωq]; simp
  · intro hω1
    apply hm
    rw [Complex.exp_eq_one_iff] at hω1
    obtain ⟨k, hk⟩ := hω1
    rw [div_eq_iff hq0] at hk
    have hmq : (m:ℂ) = (k:ℂ) * (q:ℂ) := mul_left_cancel₀ h2πi (by linear_combination hk)
    have hmk : m = k * q := by exact_mod_cast hmq
    exact ⟨k, by rw [hmk]; ring⟩

/-- **DFT inversion (step (ii) of the residue-jet obstruction):** if the DFT values
`Σ_r E_r·e^{2πir·s/q}` vanish for all `s : Fin q`, then every `E_r = 0`.  Multiply the `s`-th equation
by `e^{-2πir'·s/q}`, sum over `s`, and use character orthogonality (`exp_orthogonality`): the inner sum
is `q·δ_{r,r'}`, leaving `q·E_{r'} = 0`. -/
theorem dft_inversion {q : ℕ} (hq : 0 < q) (E : Fin q → ℂ)
    (hvan : ∀ s : Fin q, ∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))) = 0) :
    ∀ r' : Fin q, E r' = 0 := by
  intro r'
  have hinner : ∀ r : Fin q, (∑ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
      * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))))
      = if r = r' then (q:ℂ) else 0 := by
    intro r
    have hcomb : ∀ s : Fin q, Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ)))
        * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ))))
        = Complex.exp (2*(Real.pi:ℂ)*I*(((r:ℤ)-(r':ℤ) : ℤ):ℂ)*((s:ℕ)/(q:ℂ))) := by
      intro s; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [Finset.sum_congr rfl (fun s _ => hcomb s)]
    by_cases hr : r = r'
    · subst hr; simp
    · rw [if_neg hr]
      apply exp_orthogonality hq
      intro hdvd
      have h1 : (r:ℕ) < q := r.isLt
      have h2 : (r':ℕ) < q := r'.isLt
      have h3 : (r:ℤ) - (r':ℤ) ≠ 0 := by intro h; apply hr; ext; omega
      have hle : (q:ℤ) ≤ |(r:ℤ) - (r':ℤ)| :=
        Int.le_of_dvd (abs_pos.mpr h3) ((dvd_abs _ _).mpr hdvd)
      have hlt : |(r:ℤ) - (r':ℤ)| < (q:ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
      linarith
  have key : ∑ r : Fin q, E r * (if r = r' then (q:ℂ) else 0)
      = ∑ s : Fin q, (∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))))
          * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))) := by
    simp_rw [Finset.sum_mul, ← hinner, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => by ring))
  have hzero : ∑ s : Fin q, (∑ r : Fin q, E r * Complex.exp (2*(Real.pi:ℂ)*I*(r:ℕ)*((s:ℕ)/(q:ℂ))))
          * Complex.exp (-(2*(Real.pi:ℂ)*I*(r':ℕ)*((s:ℕ)/(q:ℂ)))) = 0 :=
    Finset.sum_eq_zero (fun s _ => by rw [hvan s, zero_mul])
  rw [hzero] at key
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  exact (mul_eq_zero.mp key).resolve_right (Nat.cast_ne_zero.mpr hq.ne')

/-- **The residue-`r` partial theta is a scaled theta of modulus `q²τ`:**
`Σ'_ℓ term_{qℓ+r}(w) = term_r(w) · θ(q(w+rτ), q²τ)`.  Each `(qℓ+r)²τ` splits as `r²τ + q²ℓ²τ + 2qℓrτ`,
so the sum over `ℓ` reindexes to `θ` at modulus `q²τ`.  Since `θ(·, q²τ)` has valence `1` and `term_r`
is nonvanishing, this exposes the valence structure the residue-jet independence (step (iii)) rests on. -/
theorem residue_partial_theta {q : ℕ} (hq : 0 < q) (r : ℤ) (w τ : ℂ) (hτ : 0 < τ.im) :
    ∑' ℓ : ℤ, jacobiTheta₂_term ((q:ℤ)*ℓ + r) w τ
      = jacobiTheta₂_term r w τ * jacobiTheta₂ ((q:ℂ)*(w + (r:ℂ)*τ)) ((q:ℂ)^2*τ) := by
  have hσ : 0 < ((q:ℂ)^2*τ).im := by
    rw [Complex.mul_im]
    have h1 : ((q:ℂ)^2).im = 0 := by
      rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring]; exact Complex.natCast_im _
    have h2 : ((q:ℂ)^2).re = (q:ℝ)^2 := by
      rw [show (q:ℂ)^2 = ((q^2 : ℕ):ℂ) from by push_cast; ring, Complex.natCast_re]; push_cast; ring
    rw [h1, h2, zero_mul, add_zero]
    exact mul_pos (by positivity) hτ
  have hpt : ∀ ℓ : ℤ, jacobiTheta₂_term ((q:ℤ)*ℓ + r) w τ
      = jacobiTheta₂_term r w τ * jacobiTheta₂_term ℓ ((q:ℂ)*(w + (r:ℂ)*τ)) ((q:ℂ)^2*τ) := by
    intro ℓ; simp only [jacobiTheta₂_term]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [tsum_congr hpt, tsum_mul_left, (hasSum_jacobiTheta₂_term _ hσ).tsum_eq]

end LyubarskiiNes.FrobeniusDeterminant.FrobeniusFactor
