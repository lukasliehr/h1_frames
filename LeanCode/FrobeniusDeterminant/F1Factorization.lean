import LeanCode.FrobeniusDeterminant.F1Proportional

open Complex Matrix
open scoped Real

namespace LyubarskiiNes.FrobeniusDeterminant

open LyubarskiiNes.FrobeniusDeterminant.FrobeniusFactor LyubarskiiNes.FrobeniusDeterminant.LevelPComponent
  LyubarskiiNes.FrobeniusDeterminant.ThetaDimension

/-! ## Oddness of the odd-theta section -/

/-- **`ϑ_Ω` is odd**: `ϑ_Ω(-z) = -ϑ_Ω(z)`.  Derived from the closed form
`ϑ_Ω(z) = e^{πiΩ/4 + πiz}·θ_Ω(z + (1+Ω)/2)`, the evenness of `θ`, and its
quasi-periodicity under `±1` and `±Ω`. -/
theorem oddTheta_neg (Ω z : ℂ) :
    LyubarskiiNes.ThetaFunctions.oddTheta Ω (-z) = -LyubarskiiNes.ThetaFunctions.oddTheta Ω z := by
  simp only [LyubarskiiNes.ThetaFunctions.oddTheta_apply]
  set W : ℂ := z + (1 + Ω) / 2 with hW
  -- Step A: θ_Ω(-z + (1+Ω)/2) = θ_Ω(z - (1+Ω)/2) = θ_Ω(W - 1 - Ω)  (evenness)
  have heven : LyubarskiiNes.ThetaFunctions.theta Ω (-z + (1 + Ω) / 2)
      = LyubarskiiNes.ThetaFunctions.theta Ω (W - 1 - Ω) := by
    have := LyubarskiiNes.ThetaFunctions.theta_neg_eq Ω (z - (1 + Ω) / 2)
    rw [show -(z - (1 + Ω) / 2) = -z + (1 + Ω) / 2 by ring] at this
    rw [this, hW]; congr 1; ring
  -- Step B: θ_Ω(W - 1) = θ_Ω(W)   (period 1)
  have hper1 : LyubarskiiNes.ThetaFunctions.theta Ω (W - 1) = LyubarskiiNes.ThetaFunctions.theta Ω W := by
    have := LyubarskiiNes.ThetaFunctions.theta_add_one_eq Ω (W - 1)
    rw [show W - 1 + 1 = W by ring] at this; exact this.symm
  -- Step C: θ_Ω((W-1) - Ω) = e^{πi(2(W-1) - Ω)}·θ_Ω(W-1)
  have htau : LyubarskiiNes.ThetaFunctions.theta Ω ((W - 1) - Ω)
      = Complex.exp ((Real.pi : ℂ) * I * (2 * (W - 1) - Ω)) * LyubarskiiNes.ThetaFunctions.theta Ω (W - 1) := by
    have h := LyubarskiiNes.ThetaFunctions.theta_add_tau_eq Ω ((W - 1) - Ω)
    rw [show (W - 1) - Ω + Ω = W - 1 by ring] at h
    -- h : θ(W-1) = e^{-πi(Ω + 2(W-1-Ω))}·θ(W-1-Ω)
    rw [h, ← mul_assoc, ← Complex.exp_add,
      show (Real.pi : ℂ) * I * (2 * (W - 1) - Ω)
          + -↑Real.pi * I * (Ω + 2 * (W - 1 - Ω)) = 0 by ring,
      Complex.exp_zero, one_mul]
  -- Assemble: θ_Ω(-z + (1+Ω)/2) = e^{πi(2(W-1)-Ω)}·θ_Ω(W)
  have hcombine : LyubarskiiNes.ThetaFunctions.theta Ω (-z + (1 + Ω) / 2)
      = Complex.exp ((Real.pi : ℂ) * I * (2 * (W - 1) - Ω)) * LyubarskiiNes.ThetaFunctions.theta Ω W := by
    rw [heven, show W - 1 - Ω = (W - 1) - Ω by ring, htau, hper1]
  rw [hcombine, ← mul_assoc, ← Complex.exp_add]
  -- collect the exponent and pull out the -1 from e^{-πi}
  rw [show (Real.pi : ℂ) * I * Ω / 4 + ↑Real.pi * I * -z
        + (Real.pi : ℂ) * I * (2 * (W - 1) - Ω)
      = (↑Real.pi * I * Ω / 4 + ↑Real.pi * I * z) + (-(↑Real.pi * I)) by rw [hW]; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-! ## STEP 1 — row-0 evaluation of the Frobenius determinant

Writing `i₀ = ⟨0,hp⟩`, `frob_proportional` at `w = u i₀` together with
`frobMatrix_det_update_eq_levelPTheta` (identity update) yields the "first-row" factorization
`det u = k(u) · Ξ_p(pτ)(∑u) · ∏_{s≠0} ϑ_{pτ}(u s − u i₀)`. -/

theorem frobMatrix_det_eq_scalar_mul_row0 {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) :
    ∃ k : ℂ, (frobMatrix p τ u).det
      = k * XiSection p ((p : ℂ) * τ) (∑ s, u s)
        * ∏ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
            LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u ⟨0, hp⟩) := by
  classical
  obtain ⟨k, hk⟩ := frob_proportional hp τ hτ u
  refine ⟨k, ?_⟩
  set i₀ : Fin p := ⟨0, hp⟩ with hi0
  -- det u = levelPTheta ... (u i₀)
  have hupd : Function.update u i₀ (u i₀) = u := Function.update_eq_self i₀ u
  have hdet : (frobMatrix p τ u).det
      = levelPTheta p (frobDetCoeff hp τ u) τ (u i₀) := by
    have h := frobMatrix_det_update_eq_levelPTheta hp τ hτ u (u i₀)
    rw [hupd] at h
    rw [h]; rfl
  rw [hdet, hk (u i₀)]
  -- expand frobComparison at w = u i₀
  unfold frobComparison
  -- the Ξ argument: u i₀ + ∑_{s≠i₀} u s = ∑ u
  have hsum : u i₀ + ∑ s ∈ Finset.univ.erase i₀, u s = ∑ s, u s := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  rw [hsum]
  ring

/-! ## STEP 2 — symmetry of `det` and of the double `ϑ`-product -/

/-- Permuting the argument vector permutes the rows of the Frobenius matrix. -/
theorem frobMatrix_comp_perm {p : ℕ} (τ : ℂ) (u : Fin p → ℂ) (σ : Equiv.Perm (Fin p)) :
    frobMatrix p τ (u ∘ σ) = (frobMatrix p τ u).submatrix σ id := by
  ext r s
  simp only [frobMatrix, Matrix.of_apply, Matrix.submatrix_apply, Function.comp_apply, id]

/-- **`det` transforms by the sign of the permutation.** -/
theorem frobMatrix_det_comp_perm {p : ℕ} (τ : ℂ) (u : Fin p → ℂ) (σ : Equiv.Perm (Fin p)) :
    (frobMatrix p τ (u ∘ σ)).det = (Equiv.Perm.sign σ : ℂ) * (frobMatrix p τ u).det := by
  rw [frobMatrix_comp_perm, Matrix.det_permute]

/-- **The theta-Vandermonde double product transforms by the sign of `σ`.**  Because `ϑ` is odd,
the pair-antisymmetric factor `f i j = ϑ_{pτ}(u j − u i)` satisfies `f i j = −f j i`, so
`Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod` applies. -/
theorem oddThetaVandermonde_comp_perm {p : ℕ} (τ : ℂ) (u : Fin p → ℂ)
    (σ : Equiv.Perm (Fin p)) :
    (∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
        LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) ((u ∘ σ) s - (u ∘ σ) r))
      = (Equiv.Perm.sign σ : ℂ)
        * ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
            LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r) := by
  set f : Fin p → Fin p → ℂ :=
    fun i j => LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u j - u i) with hf
  have hodd : ∀ i j, f i j = -f j i := by
    intro i j
    simp only [hf]
    rw [show u i - u j = -(u j - u i) by ring, oddTheta_neg, neg_neg]
  have hkey := Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod σ hodd
  -- rewrite the composed product into f (σ i)(σ j) form
  simpa only [hf, Function.comp_apply] using hkey

/-! ## The denominator and the `r = 0` block

`denom u = Ξ_p(pτ)(∑u) · ∏_{r<s} ϑ_{pτ}(u s − u r)`.  Its `r = 0` block coincides with the
single product appearing in STEP 1, because in `Fin p` the strict-upper set of the minimum
`⟨0,hp⟩` is `univ.erase ⟨0,hp⟩`. -/

/-- The Frobenius factorization denominator. -/
noncomputable def denomFn (p : ℕ) (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) : ℂ :=
  XiSection p ((p : ℂ) * τ) (∑ s, u s)
    * ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
        LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)

/-- In `Fin p` the set `Ioi ⟨0,hp⟩` equals `univ.erase ⟨0,hp⟩`. -/
theorem Ioi_zero_eq_erase {p : ℕ} (hp : 0 < p) :
    Finset.Ioi (⟨0, hp⟩ : Fin p) = Finset.univ.erase (⟨0, hp⟩ : Fin p) := by
  ext s
  simp only [Finset.mem_Ioi, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [Fin.lt_def, ne_eq, Fin.ext_iff]
  show (0 : ℕ) < s.val ↔ ¬ s.val = 0
  omega

/-- **`denom` factored across its `r = 0` block.**  Splitting the outer product at `r = ⟨0,hp⟩`
exposes the STEP-1 single product `∏_{s≠0} ϑ(u s − u₀)` times the remaining blocks. -/
theorem denomFn_split_row0 {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) :
    denomFn p hp τ u
      = XiSection p ((p : ℂ) * τ) (∑ s, u s)
        * ((∏ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u ⟨0, hp⟩))
          * ∏ r ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p), ∏ s ∈ Finset.Ioi r,
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)) := by
  classical
  unfold denomFn
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨0, hp⟩ : Fin p)), mul_comm,
    Ioi_zero_eq_erase hp]

/-! ## STEP 3 + STEP 4 — the constant, and the final factorization

The remaining content is the genuine analytic frontier.  STEP 1 gives, for every `u`, a scalar
`k(u)` with `det u = k(u) · Ξ_p(pτ)(∑u) · ∏_{s≠0} ϑ(u s − u₀)`, i.e. (via `denomFn_split_row0`)
`det u = (k(u) / Prest(u)) · denom u`, where `Prest(u) = ∏_{r≠0} ∏_{s∈Ioi r} ϑ(u s − u r)`.

*STEP 3* (constancy):  `det / denom` is independent of `u₀` (STEP 1: `k(u)` does not see `u₀`) and
symmetric under `σ ∈ S_p` (STEP 2: `det` and the `ϑ`-Vandermonde both pick up `sign σ`, which
cancels; `∑u` and `Ξ` are symmetric), so it is independent of every coordinate, hence constant on
the connected generic locus `{denom ≠ 0}`; being a ratio of entire functions agreeing there, it
extends to all `u` by density/continuity.

*STEP 4* (`C ≠ 0`):  `det` is not identically zero — else the columns `w ↦ ϑ₂(w + s/p)` = `thetaCol`
would be linearly dependent, contradicting `ThetaDimension.thetaCol_linearIndependent`.  Evaluating
the constancy at a point with `det ≠ 0` and `denom ≠ 0` forces the constant nonzero.

Both are packaged as the single analytic input below. -/

/-! ## STEP 3 helper lemmas — the coordinate invariances of `det / denomFn` -/

/-- The "remaining" `ϑ`-Vandermonde block, over the rows `r ≠ 0`. -/
noncomputable def Prest {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) : ℂ :=
  ∏ r ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p), ∏ s ∈ Finset.Ioi r,
    LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)

/-- **`frobComparison` is independent of `u₀`.**  It only reads the erased sum/product over `s ≠ 0`. -/
theorem frobComparison_update_zero {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (a : ℂ) :
    frobComparison p hp τ (Function.update u ⟨0, hp⟩ a) = frobComparison p hp τ u := by
  classical
  funext w
  unfold frobComparison
  have hE : ∀ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p),
      Function.update u ⟨0, hp⟩ a s = u s := by
    intro s hs
    rw [Function.update_apply, if_neg (Finset.mem_erase.mp hs).1]
  rw [Finset.sum_congr rfl hE, Finset.prod_congr rfl (fun s hs => by rw [hE s hs])]

/-- Feeding `w` into the level-`p` det-section reproduces `det (update u₀ w)`. -/
theorem det_update_eq_levelP {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (w : ℂ) :
    (frobMatrix p τ (Function.update u ⟨0, hp⟩ w)).det
      = levelPTheta p (frobDetCoeff hp τ u) τ w :=
  frobMatrix_det_update_eq_levelPTheta hp τ hτ u w

/-- **`denomFn` transforms by the sign of the permutation.**  `Ξ_p(∑u)` is invariant (`∑` is
symmetric), and the `ϑ`-Vandermonde double product picks up `sign σ` (STEP 2). -/
theorem denomFn_comp_perm {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) (σ : Equiv.Perm (Fin p)) :
    denomFn p hp τ (u ∘ σ) = (Equiv.Perm.sign σ : ℂ) * denomFn p hp τ u := by
  unfold denomFn
  have hsum : (∑ s, (u ∘ σ) s) = ∑ s, u s := by
    simpa using (Equiv.sum_comp σ u)
  rw [hsum, oddThetaVandermonde_comp_perm τ u σ]
  ring

/-- **`denomFn` splits through the row-`0` block `frobComparison(·)(v₀)`.**
`denomFn v = frobComparison p hp τ v (v ⟨0,hp⟩) · Prest v`. -/
theorem denomFn_eq_frobComparison_mul_Prest {p : ℕ} (hp : 0 < p) (τ : ℂ) (u : Fin p → ℂ) :
    denomFn p hp τ u
      = frobComparison p hp τ u (u ⟨0, hp⟩) * Prest hp τ u := by
  classical
  rw [denomFn_split_row0 hp τ u]
  unfold frobComparison Prest
  set i₀ : Fin p := ⟨0, hp⟩ with hi0
  have hsum : u i₀ + ∑ s ∈ Finset.univ.erase i₀, u s = ∑ s, u s := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  rw [hsum]; ring

/-- **The scalar `k` is shared** between `u` and `update u ⟨0,hp⟩ a`, and captures both
determinants: there is a single `k` with `det (update u ⟨0,hp⟩ w) = k · frobComparison p hp τ u w`
for every `w`.  (Because `frobDetCoeff` and `frobComparison` ignore row `0`.) -/
theorem exists_shared_k {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (u : Fin p → ℂ) :
    ∃ k : ℂ, ∀ w : ℂ,
      (frobMatrix p τ (Function.update u ⟨0, hp⟩ w)).det
        = k * frobComparison p hp τ u w := by
  obtain ⟨k, hk⟩ := frob_proportional hp τ hτ u
  exact ⟨k, fun w => by rw [det_update_eq_levelP hp τ hτ u w, hk w]⟩

/-- **Cross-multiplication in coordinate `0` (unconditional).**  Moving `u₀ ↦ a` gives
`det u · denomFn (update u ⟨0,hp⟩ a) = det (update u ⟨0,hp⟩ a) · denomFn u`.  Proof: both `det u`
and `det (update u ⟨0,hp⟩ a)` are `k` times a `frobComparison`-value at `u₀` resp. `a`, with the
*same* `k`; and each `denomFn` is that same `frobComparison`-value times the common `Prest`. -/
theorem det_denomFn_cross_update_zero {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (a : ℂ) :
    (frobMatrix p τ u).det * denomFn p hp τ (Function.update u ⟨0, hp⟩ a)
      = (frobMatrix p τ (Function.update u ⟨0, hp⟩ a)).det * denomFn p hp τ u := by
  classical
  set i₀ : Fin p := ⟨0, hp⟩ with hi0
  set v : Fin p → ℂ := Function.update u i₀ a with hv
  obtain ⟨k, hk⟩ := exists_shared_k hp τ hτ u
  -- det u = det (update u i₀ (u i₀)) = k · frobComparison u (u i₀)
  have hdetu : (frobMatrix p τ u).det = k * frobComparison p hp τ u (u i₀) := by
    have := hk (u i₀); rwa [Function.update_eq_self i₀ u] at this
  -- det v = det (update u i₀ a) = k · frobComparison u a
  have hdetv : (frobMatrix p τ v).det = k * frobComparison p hp τ u a := hk a
  -- denomFn u = frobComparison u (u i₀) · Prest u
  have hdu := denomFn_eq_frobComparison_mul_Prest hp τ u
  -- denomFn v = frobComparison v (v i₀) · Prest v ; and v i₀ = a, frobComparison v = frobComparison u,
  -- Prest v = Prest u.
  have hvi0 : v i₀ = a := by rw [hv, Function.update_self]
  have hcmpv : frobComparison p hp τ v = frobComparison p hp τ u :=
    frobComparison_update_zero hp τ u a
  have hPrestv : Prest hp τ v = Prest hp τ u := by
    unfold Prest
    refine Finset.prod_congr rfl (fun r hr => Finset.prod_congr rfl (fun s hs => ?_))
    have hrne : r ≠ i₀ := (Finset.mem_erase.mp hr).1
    have hsne : s ≠ i₀ := by
      have hrs : r < s := Finset.mem_Ioi.mp hs
      have hrs' : r.val < s.val := hrs
      intro hsi0
      have : s.val = 0 := congrArg Fin.val hsi0
      omega
    rw [hv, Function.update_apply, Function.update_apply, if_neg hsne, if_neg hrne]
  have hdv : denomFn p hp τ v = frobComparison p hp τ u a * Prest hp τ u := by
    rw [denomFn_eq_frobComparison_mul_Prest hp τ v, hvi0, hcmpv, hPrestv]
  rw [hdetu, hdetv, hdu, hdv]; ring

/-! ## Analyticity of `det` and `denomFn` on `ℂ^p = (Fin p → ℂ)` -/

/-- Each Frobenius entry `u ↦ ϑ₂(u r + s/p, τ)` is analytic in `u`. -/
theorem entry_analytic {p : ℕ} (τ : ℂ) (hτ : 0 < τ.im) (r s : Fin p) (u0 : Fin p → ℂ) :
    AnalyticAt ℂ (fun u : Fin p → ℂ => jacobiTheta₂ (u r + ((s : ℕ) : ℂ) / (p : ℂ)) τ) u0 := by
  have hproj : AnalyticAt ℂ (fun u : Fin p → ℂ => u r) u0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) r).analyticAt _
  have harg : AnalyticAt ℂ (fun u : Fin p → ℂ => u r + ((s : ℕ) : ℂ) / (p : ℂ)) u0 :=
    hproj.add analyticAt_const
  have hth : AnalyticOnNhd ℂ (fun z => jacobiTheta₂ z τ) Set.univ :=
    LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hτ
  exact (hth _ (Set.mem_univ _)).comp harg

/-- The Frobenius determinant `u ↦ det (frobMatrix p τ u)` is analytic in `u`. -/
theorem det_analytic {p : ℕ} (τ : ℂ) (hτ : 0 < τ.im) (u0 : Fin p → ℂ) :
    AnalyticAt ℂ (fun u : Fin p → ℂ => (frobMatrix p τ u).det) u0 := by
  have hentry : ∀ (r s : Fin p), AnalyticAt ℂ (fun u : Fin p → ℂ => (frobMatrix p τ u) r s) u0 := by
    intro r s
    simp only [frobMatrix, Matrix.of_apply]
    exact entry_analytic τ hτ r s u0
  have hdet : (fun u : Fin p → ℂ => (frobMatrix p τ u).det)
      = fun u => ∑ σ : Equiv.Perm (Fin p),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin p, (frobMatrix p τ u) (σ i) i := by
    funext u; rw [Matrix.det_apply']
  rw [hdet]
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hentry (σ i) i

/-- `ϑ_Ω` is analytic on all of `ℂ`. -/
theorem oddTheta_analyticOnNhd (Ω : ℂ) (hΩ : 0 < Ω.im) :
    AnalyticOnNhd ℂ (LyubarskiiNes.ThetaFunctions.oddTheta Ω) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (fun z => differentiableAt_oddTheta Ω z hΩ)

/-- `Ξ_p(Ω)` is analytic on all of `ℂ`. -/
theorem XiSection_analyticOnNhd (p : ℕ) (Ω : ℂ) (hΩ : 0 < Ω.im) :
    AnalyticOnNhd ℂ (XiSection p Ω) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (fun z => differentiableAt_XiSection p Ω z hΩ)

/-- The coordinate sum `u ↦ ∑ s, u s` is analytic. -/
theorem sum_analytic {p : ℕ} (u0 : Fin p → ℂ) :
    AnalyticAt ℂ (fun u : Fin p → ℂ => ∑ s, u s) u0 := by
  apply Finset.analyticAt_fun_sum
  intro s _
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) s).analyticAt _

/-- The denominator `u ↦ denomFn p hp τ u` is analytic in `u`. -/
theorem denomFn_analytic {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (u0 : Fin p → ℂ) :
    AnalyticAt ℂ (fun u : Fin p → ℂ => denomFn p hp τ u) u0 := by
  have hΩ : 0 < ((p : ℂ) * τ).im := qtau_im_pos hp hτ
  unfold denomFn
  apply AnalyticAt.mul
  · exact (XiSection_analyticOnNhd p _ hΩ _ (Set.mem_univ _)).comp (sum_analytic u0)
  · apply Finset.analyticAt_fun_prod
    intro r _
    apply Finset.analyticAt_fun_prod
    intro s _
    have harg : AnalyticAt ℂ (fun u : Fin p → ℂ => u s - u r) u0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) s).analyticAt _).sub
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) r).analyticAt _)
    exact (oddTheta_analyticOnNhd _ hΩ _ (Set.mem_univ _)).comp harg

/-! ## STEP A — the determinant vanishes on the divisor `{denomFn = 0}` -/

/-- **STEP A.**  If `denomFn u = 0` then `det u = 0`.  Either the `Ξ`-factor vanishes (then the
STEP-1 row-0 factorization gives `det u = 0`), or some `ϑ(u s − u r) = 0` with `r < s`, forcing
rows `r,s` of the Frobenius matrix onto a common `Λ_{pτ}`-coset, whence `det u = 0`. -/
theorem det_eq_zero_of_denomFn_eq_zero {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (hden : denomFn p hp τ u = 0) :
    (frobMatrix p τ u).det = 0 := by
  classical
  have hΩ : 0 < ((p : ℂ) * τ).im := qtau_im_pos hp hτ
  -- denomFn = Ξ(∑u) · ∏∏ ϑ = 0 ⟹ one of the factors is 0
  rw [denomFn] at hden
  rcases mul_eq_zero.mp hden with hXi | hprod
  · -- Ξ(∑u) = 0 : STEP-1 factorization makes det = 0
    obtain ⟨k, hk⟩ := frobMatrix_det_eq_scalar_mul_row0 hp τ hτ u
    rw [hk, hXi]; ring
  · -- some double-product factor vanishes: find r < s with ϑ(u s − u r) = 0
    obtain ⟨r, -, hr⟩ := Finset.prod_eq_zero_iff.mp hprod
    obtain ⟨s, hs, hrs⟩ := Finset.prod_eq_zero_iff.mp hr
    have hlt : r < s := Finset.mem_Ioi.mp hs
    -- ϑ(u s − u r) = 0 ⟹ u s − u r ∈ Λ_{pτ}
    rw [oddTheta_eq_zero_iff_of_im_pos hΩ] at hrs
    obtain ⟨m, n, hmn⟩ := hrs
    have hcoset : u s - u r = (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ) := hmn
    have hsr : s ≠ r := (ne_of_lt hlt).symm
    have hFrob_eq_Fmat : frobMatrix p τ u = ThetaDimension.Fmat τ p u := by
      funext a b
      simp only [frobMatrix, Matrix.of_apply, ThetaDimension.Fmat]
    rw [hFrob_eq_Fmat]
    exact ThetaDimension.Fmat_det_eq_zero_of_coset τ p u hsr ⟨m, n, hcoset⟩

/-- **STEP A, contrapositive.**  `det u ≠ 0 ⟹ denomFn u ≠ 0`. -/
theorem denomFn_ne_zero_of_det_ne_zero {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) (hdet : (frobMatrix p τ u).det ≠ 0) :
    denomFn p hp τ u ≠ 0 :=
  fun hden => hdet (det_eq_zero_of_denomFn_eq_zero hp τ hτ u hden)

/-! ## STEP B — a point where the Frobenius determinant does not vanish

The `p` primitive theta columns `thetaCol τ p s` are `ℂ`-linearly independent
(`ThetaDimension.thetaCol_linearIndependent`).  We first repackage this as *evaluation
independence* (`thetaCol_eval_indep`), then prove the general "Haar/Chebyshev" sampling lemma
(`exists_sample_det_ne_zero`): an evaluation-independent finite family of functions admits a
nonsingular sampling matrix.  Applying it to the theta columns gives the sought sample. -/

/-- **Evaluation independence of the theta columns**, extracted from
`thetaCol_linearIndependent`: no nonzero coefficient vector makes `∑ s, a s · thetaCol s`
vanish identically. -/
theorem thetaCol_eval_indep {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im)
    (a : Fin p → ℂ) (h : ∀ z : ℂ, ∑ s : Fin p, a s * thetaCol τ p ((s : ℕ)) z = 0) :
    a = 0 := by
  have hli := thetaCol_linearIndependent hp hτ
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : (∑ s : Fin p, a s • thetaColElt hp hτ s) = 0 := by
    apply Subtype.ext
    rw [AddSubmonoid.coe_finsetSum, Submodule.coe_zero]
    funext z
    rw [Pi.zero_apply, Finset.sum_apply]
    have hpt : ∀ s : Fin p,
        ((a s • thetaColElt hp hτ s : ThetaSpace p 0 ((p : ℂ) * τ)) : ℂ → ℂ) z
          = a s * thetaCol τ p ((s : ℕ)) z := by
      intro s
      rw [Submodule.coe_smul_of_tower]
      simp only [thetaColElt, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun s _ => hpt s)]
    exact h z
  funext s
  exact hli a hsum s

/-- **The Haar/Chebyshev sampling lemma.**  A family `f : Fin n → (ℂ → ℂ)` that is
evaluation-independent admits sample points at which the sampling matrix `(f s (x r))_{r,s}` is
nonsingular.  Induction on `n`: strip the first column, use the IH on the remaining `n` functions
to sample the bottom `n × n` block; Laplace-expanding the new top row, the coefficient of `f 0(z)`
is that nonzero minor, so `z ↦ det` is a nontrivial combination of the `f s`, hence not identically
zero by independence; pick a nonvanishing `z`. -/
theorem exists_sample_det_ne_zero :
    ∀ (n : ℕ) (f : Fin n → (ℂ → ℂ)),
      (∀ a : Fin n → ℂ, (∀ z : ℂ, ∑ s : Fin n, a s * f s z = 0) → a = 0) →
      ∃ x : Fin n → ℂ, (Matrix.of fun r s => f s (x r)).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro f _
    exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro f hindep
    have htail_indep : ∀ a : Fin n → ℂ,
        (∀ z : ℂ, ∑ s : Fin n, a s * f s.succ z = 0) → a = 0 := by
      intro a ha
      have hext : (Fin.cons 0 a : Fin (n+1) → ℂ) = 0 := by
        apply hindep
        intro z
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
        exact ha z
      funext s
      have := congrFun hext s.succ
      rwa [Fin.cons_succ, Pi.zero_apply] at this
    obtain ⟨x', hx'⟩ := ih (fun s => f s.succ) htail_indep
    set M : ℂ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      fun z => Matrix.of fun r s => f s ((Fin.cons z x' : Fin (n+1) → ℂ) r) with hM
    set g : ℂ → ℂ := fun z => (M z).det with hg
    have hlap : ∀ z : ℂ, g z
        = ∑ j : Fin (n+1),
            (-1 : ℂ) ^ (j : ℕ) * f j z * ((M z).submatrix Fin.succ j.succAbove).det := by
      intro z
      simp only [hg]
      rw [Matrix.det_succ_row_zero (M z)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 2
    have hminor : ∀ z : ℂ, ∀ j : Fin (n+1),
        ((M z).submatrix Fin.succ j.succAbove).det
          = (Matrix.of fun r s => f (j.succAbove s) (x' r)).det := by
      intro z j
      congr 1
    have hc0 : (Matrix.of fun r s => f ((0 : Fin (n+1)).succAbove s) (x' r)).det
        = (Matrix.of fun r s => f s.succ (x' r)).det := by
      congr 1
    set c : Fin (n+1) → ℂ :=
      fun j => (-1 : ℂ) ^ (j : ℕ) * (Matrix.of fun r s => f (j.succAbove s) (x' r)).det with hc
    have hgc : ∀ z : ℂ, g z = ∑ j : Fin (n+1), c j * f j z := by
      intro z
      rw [hlap z]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hminor z j, hc]; ring
    have hc0ne : c 0 ≠ 0 := by
      rw [hc]
      simp only [Fin.val_zero, pow_zero, one_mul, hc0]
      exact hx'
    have hgne : ∃ z : ℂ, g z ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hcdep : c = 0 := by
        apply hindep
        intro z
        rw [← hgc z]; exact hall z
      exact hc0ne (congrFun hcdep 0)
    obtain ⟨z0, hz0⟩ := hgne
    refine ⟨Fin.cons z0 x', ?_⟩
    have heq : (Matrix.of fun r s => f s ((Fin.cons z0 x' : Fin (n+1) → ℂ) r)).det = g z0 := by
      simp only [hg, hM]
    rw [heq]; exact hz0

/-- **STEP B.**  There is a point at which the Frobenius determinant is nonzero.  The Frobenius
matrix is the sampling matrix `(thetaCol τ p s (u r))_{r,s}` of the linearly independent theta
columns, so `exists_sample_det_ne_zero` provides the point. -/
theorem exists_det_ne_zero {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ u : Fin p → ℂ, (frobMatrix p τ u).det ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_sample_det_ne_zero p (fun s => thetaCol τ p ((s : ℕ)))
    (fun a ha => thetaCol_eval_indep hp hτ a ha)
  refine ⟨u, ?_⟩
  have hmat : (Matrix.of fun (r : Fin p) (s : Fin p) => thetaCol τ p ((s : ℕ)) (u r))
      = frobMatrix p τ u := by
    funext r s
    simp only [Matrix.of_apply, frobMatrix, thetaCol]
  rwa [hmat] at hu

/-! ## STEP C — local constancy of `det / denomFn` near a nonsingular point -/

/-- **Coordinate-`i` cross-multiplication (unconditional).**  Moving coordinate `i` from `b` to `a`
leaves `det · denomFn` symmetric: conjugating by `swap ⟨0,hp⟩ i` reduces to the coordinate-`0`
identity, and the two `sign σ` factors cancel. -/
theorem det_denomFn_cross_coord {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (u : Fin p → ℂ)
    (i : Fin p) (a b : ℂ) :
    (frobMatrix p τ (Function.update u i a)).det * denomFn p hp τ (Function.update u i b)
      = (frobMatrix p τ (Function.update u i b)).det * denomFn p hp τ (Function.update u i a) := by
  classical
  set σ : Equiv.Perm (Fin p) := Equiv.swap (⟨0, hp⟩ : Fin p) i with hσ
  set v : Fin p → ℂ := u ∘ σ with hv
  have hrw : ∀ w : ℂ, Function.update u i w = (Function.update v ⟨0, hp⟩ w) ∘ σ := by
    intro w; rw [hv, hσ]
    -- update u i w = (update (u∘σ) 0 w) ∘ σ  since σ = swap 0 i is an involution
    have hkey := Function.update_comp_equiv u (σ : Fin p ≃ Fin p) i w
    rw [show σ.symm i = (⟨0, hp⟩ : Fin p) by
          rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]] at hkey
    rw [← hkey, Function.comp_assoc]
    have hσσ : (σ : Fin p → Fin p) ∘ (σ : Fin p → Fin p) = id :=
      funext (fun x => by rw [Function.comp_apply, hσ, Equiv.swap_apply_self, id])
    rw [hσσ, Function.comp_id]
  rw [hrw a, hrw b]
  -- coordinate-0 cross-multiplication of `v`, transported by `σ`
  have hcu := det_denomFn_cross_update_zero hp τ hτ (Function.update v ⟨0, hp⟩ b) a
  rw [Function.update_idem] at hcu
  -- hcu : det(update v 0 b)·denomFn(update v 0 a) = det(update v 0 a)·denomFn(update v 0 b)
  rw [frobMatrix_det_comp_perm τ _ σ, frobMatrix_det_comp_perm τ _ σ,
    denomFn_comp_perm hp τ _ σ, denomFn_comp_perm hp τ _ σ]
  -- both sides carry (sign σ)^2; cancel and apply hcu
  rw [show (Equiv.Perm.sign σ : ℂ) * (frobMatrix p τ (Function.update v ⟨0, hp⟩ a)).det
        * ((Equiv.Perm.sign σ : ℂ) * denomFn p hp τ (Function.update v ⟨0, hp⟩ b))
      = (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)
        * ((frobMatrix p τ (Function.update v ⟨0, hp⟩ a)).det
          * denomFn p hp τ (Function.update v ⟨0, hp⟩ b)) by ring,
    show (Equiv.Perm.sign σ : ℂ) * (frobMatrix p τ (Function.update v ⟨0, hp⟩ b)).det
        * ((Equiv.Perm.sign σ : ℂ) * denomFn p hp τ (Function.update v ⟨0, hp⟩ a))
      = (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)
        * ((frobMatrix p τ (Function.update v ⟨0, hp⟩ b)).det
          * denomFn p hp τ (Function.update v ⟨0, hp⟩ a)) by ring]
  rw [hcu]

/-- The "prefix mix" between a reference `r0` and `u` along a set `S` of coordinates:
`mixCoord r0 u S i = u i` if `i ∈ S`, else `r0 i`. -/
noncomputable def mixCoord {p : ℕ} (r0 u : Fin p → ℂ) (S : Finset (Fin p)) : Fin p → ℂ :=
  fun i => if i ∈ S then u i else r0 i

/-- **STEP C — chaining.**  On the locus where every prefix mix has non-vanishing `denomFn`,
the ratio `det / denomFn` at `mixCoord r0 u S` equals its value at `r0`.  Proof by induction on
`S`: adding one coordinate is a single-coordinate move, closed by `det_denomFn_cross_coord`. -/
theorem det_mul_denom_mix {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (r0 u : Fin p → ℂ)
    (hr0 : denomFn p hp τ r0 ≠ 0)
    (hnz : ∀ S : Finset (Fin p), denomFn p hp τ (mixCoord r0 u S) ≠ 0) :
    ∀ S : Finset (Fin p),
      (frobMatrix p τ (mixCoord r0 u S)).det * denomFn p hp τ r0
        = (frobMatrix p τ r0).det * denomFn p hp τ (mixCoord r0 u S) := by
  classical
  intro S
  induction S using Finset.induction with
  | empty =>
    -- mixCoord r0 u ∅ = r0
    have h0 : mixCoord r0 u (∅ : Finset (Fin p)) = r0 := by
      funext i; simp [mixCoord]
    rw [h0]
  | insert i S hiS ih =>
    -- mixCoord (insert i S) = update (mixCoord S) i (u i);  mixCoord S = update (mixCoord S) i (r0 i)
    have hins : mixCoord r0 u (insert i S) = Function.update (mixCoord r0 u S) i (u i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [mixCoord, Function.update_self]
      · simp only [mixCoord, Function.update_of_ne hj, Finset.mem_insert, hj, false_or]
    have hself : mixCoord r0 u S = Function.update (mixCoord r0 u S) i (r0 i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self, mixCoord, if_neg hiS]
      · rw [Function.update_of_ne hj]
    -- single-coordinate cross-multiplication at coordinate i, a = u i, b = r0 i
    have hcross := det_denomFn_cross_coord hp τ hτ (mixCoord r0 u S) i (u i) (r0 i)
    rw [← hins, ← hself] at hcross
    -- hcross : det (mix (insert i S)) · denomFn (mix S) = det (mix S) · denomFn (mix (insert i S))
    have hSnz : denomFn p hp τ (mixCoord r0 u S) ≠ 0 := hnz S
    -- From ih: det(mix S)·denomFn r0 = det r0 · denomFn(mix S).  Combine with hcross.
    -- Goal: det(mix (insert i S))·denomFn r0 = det r0 · denomFn(mix (insert i S)).
    -- Multiply goal-LHS by denomFn(mix S) and use hcross, ih:
    have key : (frobMatrix p τ (mixCoord r0 u (insert i S))).det * denomFn p hp τ r0
          * denomFn p hp τ (mixCoord r0 u S)
        = (frobMatrix p τ r0).det * denomFn p hp τ (mixCoord r0 u (insert i S))
          * denomFn p hp τ (mixCoord r0 u S) := by
      calc (frobMatrix p τ (mixCoord r0 u (insert i S))).det * denomFn p hp τ r0
            * denomFn p hp τ (mixCoord r0 u S)
          = ((frobMatrix p τ (mixCoord r0 u (insert i S))).det
              * denomFn p hp τ (mixCoord r0 u S)) * denomFn p hp τ r0 := by ring
        _ = ((frobMatrix p τ (mixCoord r0 u S)).det
              * denomFn p hp τ (mixCoord r0 u (insert i S))) * denomFn p hp τ r0 := by rw [hcross]
        _ = ((frobMatrix p τ (mixCoord r0 u S)).det * denomFn p hp τ r0)
              * denomFn p hp τ (mixCoord r0 u (insert i S)) := by ring
        _ = ((frobMatrix p τ r0).det * denomFn p hp τ (mixCoord r0 u S))
              * denomFn p hp τ (mixCoord r0 u (insert i S)) := by rw [ih]
        _ = (frobMatrix p τ r0).det * denomFn p hp τ (mixCoord r0 u (insert i S))
              * denomFn p hp τ (mixCoord r0 u S) := by ring
    exact mul_right_cancel₀ hSnz key

/-- **The Frobenius factorization (final form).**  Fully sorry-free.  From STEP B
(`exists_det_ne_zero`) take a point `r0` with `det r0 ≠ 0`; STEP A gives `denomFn r0 ≠ 0`.  With
`C := det r0 / denomFn r0 ≠ 0`, STEP C (`det_mul_denom_mix`, coordinate-wise chaining on the locus
`{denomFn ≠ 0}`) makes the analytic functions `u ↦ det u · denomFn r0` and `u ↦ det r0 · denomFn u`
agree on a neighborhood of `r0`; the multivariate identity theorem
(`AnalyticOnNhd.eq_of_eventuallyEq`, valid because `Fin p → ℂ` is a preconnected normed `ℂ`-space)
promotes this to a global identity, whence `det u = C · denomFn u` for all `u`. -/
theorem frobenius_factorization_probe {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ u : Fin p → ℂ,
      (frobMatrix p τ u).det =
        C * XiSection p ((p : ℂ) * τ) (∑ r, u r) *
          ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
            LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r) := by
  classical
  -- Reduce the target to the `denomFn` abbreviation.
  suffices h : ∃ C : ℂ, C ≠ 0 ∧ ∀ u : Fin p → ℂ,
      (frobMatrix p τ u).det = C * denomFn p hp τ u by
    obtain ⟨C, hC0, hC⟩ := h
    refine ⟨C, hC0, fun u => ?_⟩
    rw [hC u]; unfold denomFn; ring
  -- STEP B: a reference point r0 with det r0 ≠ 0
  obtain ⟨r0, hr0det⟩ := exists_det_ne_zero hp τ hτ
  -- STEP A: hence denomFn r0 ≠ 0
  have hr0den : denomFn p hp τ r0 ≠ 0 := denomFn_ne_zero_of_det_ne_zero hp τ hτ r0 hr0det
  -- The constant
  set C : ℂ := (frobMatrix p τ r0).det / denomFn p hp τ r0 with hCdef
  have hC0 : C ≠ 0 := div_ne_zero hr0det hr0den
  refine ⟨C, hC0, ?_⟩
  -- The two analytic functions g = det u · denomFn r0 and h = det r0 · denomFn u.
  set g : (Fin p → ℂ) → ℂ := fun u => (frobMatrix p τ u).det * denomFn p hp τ r0 with hg
  set hfun : (Fin p → ℂ) → ℂ := fun u => (frobMatrix p τ r0).det * denomFn p hp τ u with hh
  have hg_an : AnalyticOnNhd ℂ g Set.univ := fun u _ =>
    (det_analytic τ hτ u).mul analyticAt_const
  have hh_an : AnalyticOnNhd ℂ hfun Set.univ := fun u _ =>
    analyticAt_const.mul (denomFn_analytic hp τ hτ u)
  -- STEP C ⟹ local agreement of g and hfun near r0.
  have hev : g =ᶠ[nhds r0] hfun := by
    -- On the eventually-set where every prefix mix has denomFn ≠ 0, chaining gives the identity.
    -- Continuity: each `u ↦ denomFn (mixCoord r0 u S)` is continuous and equals `denomFn r0 ≠ 0` at r0.
    have hcont : ∀ S : Finset (Fin p),
        ∀ᶠ u in nhds r0, denomFn p hp τ (mixCoord r0 u S) ≠ 0 := by
      intro S
      have hmixcont : Continuous (fun u : Fin p → ℂ => mixCoord r0 u S) := by
        apply continuous_pi
        intro i
        by_cases hi : i ∈ S
        · simp only [mixCoord, if_pos hi]; exact continuous_apply i
        · simp only [mixCoord, if_neg hi]; exact continuous_const
      have hat : mixCoord r0 r0 S = r0 := by
        funext i; by_cases hi : i ∈ S <;> simp [mixCoord, hi]
      -- ContinuousAt at r0 from analyticity of denomFn (at the point r0 = mix r0 r0 S) composed
      -- with continuity of the mix map.
      have hden_ca : ContinuousAt (fun w : Fin p → ℂ => denomFn p hp τ w) (mixCoord r0 r0 S) := by
        rw [hat]; exact (denomFn_analytic hp τ hτ r0).continuousAt
      have hca : ContinuousAt (fun u : Fin p → ℂ => denomFn p hp τ (mixCoord r0 u S)) r0 :=
        ContinuousAt.comp (g := fun w : Fin p → ℂ => denomFn p hp τ w)
          (f := fun u : Fin p → ℂ => mixCoord r0 u S) hden_ca
          (hmixcont.continuousAt (x := r0))
      have hval : (fun u : Fin p → ℂ => denomFn p hp τ (mixCoord r0 u S)) r0 ≠ 0 := by
        show denomFn p hp τ (mixCoord r0 r0 S) ≠ 0
        rw [hat]; exact hr0den
      exact hca.eventually_ne hval
    -- Intersect over the finitely many subsets S (there are finitely many since Fin p is finite).
    have hall : ∀ᶠ u in nhds r0, ∀ S : Finset (Fin p),
        denomFn p hp τ (mixCoord r0 u S) ≠ 0 :=
      Filter.eventually_all.2 hcont
    filter_upwards [hall] with u hu
    -- chaining at S = univ gives det u · denomFn r0 = det r0 · denomFn u
    have huniv : mixCoord r0 u (Finset.univ : Finset (Fin p)) = u := by
      funext i; simp [mixCoord]
    have hchain := det_mul_denom_mix hp τ hτ r0 u hr0den (fun S => hu S) Finset.univ
    rw [huniv] at hchain
    simp only [hg, hh]; exact hchain
  -- Multivariate identity theorem: g = hfun everywhere.
  have hglob : g = hfun :=
    hg_an.eq_of_eventuallyEq hh_an hev
  -- Conclude det u = C · denomFn u for all u.
  intro u
  have := congrFun hglob u
  simp only [hg, hh] at this
  -- this : det u · denomFn r0 = det r0 · denomFn u
  rw [hCdef, div_mul_eq_mul_div, eq_div_iff hr0den, mul_comm ((frobMatrix p τ r0).det)]
  linear_combination this