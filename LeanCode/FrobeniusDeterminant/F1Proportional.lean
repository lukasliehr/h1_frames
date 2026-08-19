import LeanCode.FrobeniusDeterminant.FrobeniusFactor
import LeanCode.FrobeniusDeterminant.LevelPComponent
import LeanCode.FrobeniusDeterminant.XiSectionBase
import LeanCode.FrobeniusDeterminant.ThetaDimension3
open Complex Matrix
open scoped Real
namespace LyubarskiiNes.FrobeniusDeterminant
open LyubarskiiNes.FrobeniusDeterminant.FrobeniusFactor LyubarskiiNes.FrobeniusDeterminant.LevelPComponent LyubarskiiNes.FrobeniusDeterminant.ThetaDimension

/-!
# F1 analytic heart — proportionality via the theta-space DIMENSION route

Target: `frob_proportional`.  Abbreviate
  `D w   := levelPTheta p (frobDetCoeff hp τ u) τ w`
  `cmp w := frobComparison p hp τ u w`.

Both `D` and `cmp` lie in `ThetaSpace p 0 Ω` (`Ω = pτ`, dimension `p`) and both vanish at the
`p-1` points `u_s` (`s ≠ 0`).  Iterating `deltaX_div` drops the space `𝒯_{N+1} → 𝒯_N` at each shared
zero; after `p-1` divisions `D` and `cmp` land in the SAME `1`-dimensional `𝒯_1`, hence proportional.

Dichotomy on whether the `u_s` (`s ≠ 0`) are pairwise distinct mod the lattice `ℤ + Ωℤ`:
* not distinct ⇒ the underlying determinant has two equal rows ⇒ `D ≡ 0` ⇒ `k = 0`;
* distinct ⇒ run the `deltaX_div` chain (via the general helper below).
-/

/-- `ℂ` is uncountable (transfer along the real embedding). -/
instance uncountable_complex : Uncountable ℂ :=
  Function.Injective.uncountable (f := ((↑·) : ℝ → ℂ)) Complex.ofReal_injective

/-- Positivity of `(pτ).im`. -/
theorem pmul_im_pos' {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < ((p : ℂ) * τ).im := by
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hp) hτ

/-- **`cmp` is not identically zero.**  A countable-bad-set argument. -/
theorem frobComparison_ne_zero_somewhere {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) : ∃ w0 : ℂ, frobComparison p hp τ u w0 ≠ 0 := by
  classical
  set Ω : ℂ := (p : ℂ) * τ with hΩdef
  have hΩ : 0 < Ω.im := pmul_im_pos' hp hτ
  set S : ℂ := ∑ s ∈ Finset.univ.erase (⟨0, hp⟩ : Fin p), u s with hSdef
  set E : Finset (Fin p) := Finset.univ.erase (⟨0, hp⟩ : Fin p) with hEdef
  set Bxi : Set ℂ := (fun q : ℤ × ℤ =>
      (if p % 2 = 1 then (1 + Ω) / 2 else 0) + (q.1 : ℂ) + (q.2 : ℂ) * Ω - S) '' Set.univ with hBxi
  set Bfac : Fin p → Set ℂ := fun s => (fun q : ℤ × ℤ =>
      u s - ((q.1 : ℂ) + (q.2 : ℂ) * Ω)) '' Set.univ with hBfac
  set B : Set ℂ := Bxi ∪ ⋃ s ∈ E, Bfac s with hBdef
  have hBxiC : Bxi.Countable := by rw [hBxi]; exact (Set.countable_univ.image _)
  have hBfacC : ∀ s, (Bfac s).Countable := fun s => by
    rw [hBfac]; exact (Set.countable_univ.image _)
  have hBC : B.Countable := by
    rw [hBdef]
    exact hBxiC.union ((Set.countable_iUnion (fun s => (Set.countable_iUnion
      (fun _ => hBfacC s)))))
  have hne : B ≠ Set.univ := by
    intro h
    exact (Set.not_countable_univ (α := ℂ)) (h ▸ hBC)
  obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem B).mp hne
  refine ⟨w, ?_⟩
  rw [hBdef, Set.mem_union, not_or] at hw
  obtain ⟨hwxi, hwfac⟩ := hw
  unfold frobComparison
  rw [← hΩdef, ← hSdef, ← hEdef]
  apply mul_ne_zero
  · unfold XiSection
    by_cases hpar : p % 2 = 1
    · rw [if_pos hpar]
      intro hz
      have hjt : jacobiTheta₂ (w + S) Ω = 0 := hz
      obtain ⟨m, n, hmn⟩ := jacobiTheta₂_mem_of_eq_zero hΩ (w + S) hjt
      apply hwxi
      rw [hBxi]
      refine ⟨(m, n), Set.mem_univ _, ?_⟩
      simp only [if_pos hpar]
      rw [hΩdef] at hmn
      linear_combination (-1 : ℂ) * hmn
    · rw [if_neg hpar]
      intro hz
      rw [oddTheta_eq_zero_iff_of_im_pos hΩ] at hz
      obtain ⟨m, n, hmn⟩ := hz
      apply hwxi
      rw [hBxi]
      refine ⟨(m, n), Set.mem_univ _, ?_⟩
      simp only [if_neg hpar]
      rw [hΩdef] at hmn
      linear_combination (-1 : ℂ) * hmn
  · rw [Finset.prod_ne_zero_iff]
    intro s hs hz
    rw [oddTheta_eq_zero_iff_of_im_pos hΩ] at hz
    obtain ⟨m, n, hmn⟩ := hz
    apply hwfac
    rw [Set.mem_iUnion₂]
    refine ⟨s, hs, ?_⟩
    rw [hBfac]
    refine ⟨(m, n), Set.mem_univ _, ?_⟩
    rw [hΩdef] at hmn
    linear_combination (1 : ℂ) * hmn

/-! ## General helper: proportionality from shared zeros in `𝒯_N` -/

/-- **Proportionality in a `1`-dimensional theta space.**  If `f, g ∈ 𝒯_1(α)` and `g ≠ 0` (as a
function), then `f = k·g` for some scalar `k`.  Uses `finrank_ThetaSpace = 1`. -/
theorem thetaSpace_proportional_dim_one {T α : ℂ} (hT : 0 < T.im) {f g : ℂ → ℂ}
    (hf : f ∈ ThetaSpace 1 α T) (hg : g ∈ ThetaSpace 1 α T) (hgne : g ≠ 0) :
    ∃ k : ℂ, ∀ z, f z = k * g z := by
  classical
  haveI : FiniteDimensional ℂ (ThetaSpace 1 α T) := finiteDimensional_ThetaSpace hT 1 le_rfl α
  have hrank : Module.finrank ℂ (ThetaSpace 1 α T) = 1 := finrank_ThetaSpace hT 1 le_rfl α
  -- every vector is a multiple of a common `v`
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ℂ) (V := ThetaSpace 1 α T)).mp (le_of_eq hrank)
  obtain ⟨c, hc⟩ := hv ⟨g, hg⟩
  obtain ⟨d, hd⟩ := hv ⟨f, hf⟩
  -- `g ≠ 0` forces `c ≠ 0`
  have hgV : (⟨g, hg⟩ : ThetaSpace 1 α T) ≠ 0 := by
    intro h
    apply hgne
    have := congrArg (Subtype.val) h
    simpa using this
  have hc0 : c ≠ 0 := by
    intro h
    apply hgV
    rw [← hc, h, zero_smul]
  -- `v = c⁻¹ • ⟨g⟩`, so `⟨f⟩ = d • v = (d * c⁻¹) • ⟨g⟩`
  refine ⟨d * c⁻¹, ?_⟩
  have hvg : v = c⁻¹ • (⟨g, hg⟩ : ThetaSpace 1 α T) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hfV : (⟨f, hf⟩ : ThetaSpace 1 α T) = (d * c⁻¹) • (⟨g, hg⟩ : ThetaSpace 1 α T) := by
    rw [← hd, hvg, smul_smul]
  intro z
  have := congrArg (fun w : ThetaSpace 1 α T => (w : ℂ → ℂ) z) hfV
  simpa [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using this

/-- **General proportionality from shared zeros.**  If `f, g ∈ 𝒯_N(α)`, `g ≠ 0` as a function,
and there are `N-1` points `pts : Fin (N-1) → ℂ` with `deltaX T (pts i) (pts j) ≠ 0` for `i ≠ j`
and `f (pts i) = g (pts i) = 0` for all `i`, then `f = k·g`.  Proved by induction on `N`. -/
theorem thetaSpace_proportional_of_shared_zeros {T : ℂ} (hT : 0 < T.im) :
    ∀ (N : ℕ) (α : ℂ) (f g : ℂ → ℂ),
      f ∈ ThetaSpace (N + 1) α T → g ∈ ThetaSpace (N + 1) α T → g ≠ 0 →
      ∀ pts : Fin N → ℂ,
        (∀ i j : Fin N, i ≠ j → deltaX T (pts i) (pts j) ≠ 0) →
        (∀ i : Fin N, f (pts i) = 0) → (∀ i : Fin N, g (pts i) = 0) →
        ∃ k : ℂ, ∀ z, f z = k * g z := by
  intro N
  induction N with
  | zero =>
    intro α f g hf hg hgne pts _ _ _
    exact thetaSpace_proportional_dim_one hT hf hg hgne
  | succ M ih =>
    intro α f g hf hg hgne pts hdist hfz hgz
    -- divide both by `deltaX T (pts 0)`
    set z₀ : ℂ := pts 0 with hz0
    obtain ⟨f', hf'an, hf'fac, hf'mem⟩ := deltaX_div hT hf (hfz 0)
    obtain ⟨g', hg'an, hg'fac, hg'mem⟩ := deltaX_div hT hg (hgz 0)
    -- new base points: `pts (i+1)`
    set pts' : Fin M → ℂ := fun i => pts i.succ with hpts'
    -- `g' ≠ 0`: else `g = δ·0 = 0`
    have hg'ne : g' ≠ 0 := by
      intro h
      apply hgne
      funext z
      rw [hg'fac z, h]
      simp
    -- `deltaX T z₀ (pts i.succ) ≠ 0` since `pts 0 ≠ pts i.succ`
    have hδne : ∀ i : Fin M, deltaX T z₀ (pts i.succ) ≠ 0 := by
      intro i
      have hne : (0 : Fin (M + 1)) ≠ i.succ := by
        exact (Fin.succ_ne_zero i).symm
      exact hdist 0 i.succ hne
    -- `f'` and `g'` vanish at `pts' i`
    have hf'z : ∀ i : Fin M, f' (pts' i) = 0 := by
      intro i
      have hfac := hf'fac (pts i.succ)
      have hf0 : f (pts i.succ) = 0 := hfz i.succ
      rw [hf0] at hfac
      have := (mul_eq_zero.mp hfac.symm).resolve_left (hδne i)
      simpa [hpts'] using this
    have hg'z : ∀ i : Fin M, g' (pts' i) = 0 := by
      intro i
      have hfac := hg'fac (pts i.succ)
      have hg0 : g (pts i.succ) = 0 := hgz i.succ
      rw [hg0] at hfac
      have := (mul_eq_zero.mp hfac.symm).resolve_left (hδne i)
      simpa [hpts'] using this
    -- distinctness of the new base points
    have hdist' : ∀ i j : Fin M, i ≠ j → deltaX T (pts' i) (pts' j) ≠ 0 := by
      intro i j hij
      have : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective M h)
      exact hdist i.succ j.succ this
    -- IH gives `f' = k·g'`
    obtain ⟨k, hk⟩ := ih (α - (z₀ - 1/2 - T/2)) f' g' hf'mem hg'mem hg'ne pts' hdist' hf'z hg'z
    refine ⟨k, ?_⟩
    intro z
    rw [hf'fac z, hk z, hg'fac z]
    ring

/-! ## Membership of `D` and `cmp` in `ThetaSpace p 0 Ω` -/

/-- The automorphy factor for `𝒯_p^0(Ω)` (with `Ω = pτ`) matches the level-`p` `pτ`-multiplier. -/
theorem autFactor_p_zero_eq {p : ℕ} (τ z : ℂ) :
    autFactor p 0 ((p : ℂ) * τ) z
      = Complex.exp (-(Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * τ + 2 * (p : ℂ) * z)) := by
  unfold autFactor
  congr 1
  ring

/-- **`D = levelPTheta` lies in `ThetaSpace p 0 Ω`.** -/
theorem levelPTheta_mem_ThetaSpace {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (β : ℕ → ℂ) :
    (fun w : ℂ => levelPTheta p β τ w) ∈ ThetaSpace p 0 ((p : ℂ) * τ) := by
  refine ⟨fun z => (differentiable_levelPTheta hp β τ hτ).analyticAt z, ?_, ?_⟩
  · intro z; exact levelPTheta_add_one p β τ z
  · intro z
    show levelPTheta p β τ (z + (p : ℂ) * τ) = autFactor p 0 ((p : ℂ) * τ) z * levelPTheta p β τ z
    rw [levelPTheta_add_ptau p β τ z, autFactor_p_zero_eq τ z]

/-- **`cmp = frobComparison` lies in `ThetaSpace p 0 Ω`.** -/
theorem frobComparison_mem_ThetaSpace {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im)
    (u : Fin p → ℂ) :
    (fun w : ℂ => frobComparison p hp τ u w) ∈ ThetaSpace p 0 ((p : ℂ) * τ) := by
  refine ⟨fun z => (differentiable_frobComparison hp τ hτ u).analyticAt z, ?_, ?_⟩
  · intro z; exact frobComparison_add_one p hp τ u z
  · intro z
    show frobComparison p hp τ u (z + (p : ℂ) * τ)
        = autFactor p 0 ((p : ℂ) * τ) z * frobComparison p hp τ u z
    rw [frobComparison_add_ptau p hp τ u z, autFactor_p_zero_eq τ z]

/-! ## The final proportionality -/

/-- **`frob_proportional`.**  For all `u` (no genericity hypotheses), the level-`p` determinant
section is a scalar multiple of the comparison function. -/
theorem frob_proportional {p : ℕ} (hp : 0 < p) (τ : ℂ) (hτ : 0 < τ.im) (u : Fin p → ℂ) :
    ∃ k : ℂ, ∀ w : ℂ,
      levelPTheta p (frobDetCoeff hp τ u) τ w = k * frobComparison p hp τ u w := by
  classical
  have hΩ : 0 < ((p : ℂ) * τ).im := pmul_im_pos' hp hτ
  set D : ℂ → ℂ := fun w => levelPTheta p (frobDetCoeff hp τ u) τ w with hD
  set cmp : ℂ → ℂ := fun w => frobComparison p hp τ u w with hcmp
  -- write `p = q + 1`
  obtain ⟨q, hpq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  -- an index map `Fin q → Fin p` whose image avoids `0` (the nonzero rows `s ≠ 0`)
  set idx : Fin q → Fin p := fun i => Fin.cast hpq.symm i.succ with hidx
  have hidx_ne0 : ∀ i : Fin q, idx i ≠ ⟨0, hp⟩ := by
    intro i hcontra
    have : (Fin.cast hpq.symm i.succ).val = (⟨0, hp⟩ : Fin p).val := congrArg Fin.val hcontra
    simp only [Fin.val_cast, Fin.val_succ] at this
    omega
  have hidx_inj : Function.Injective idx := by
    intro i j hij
    have : (Fin.cast hpq.symm i.succ).val = (Fin.cast hpq.symm j.succ).val := congrArg Fin.val hij
    simp only [Fin.val_cast, Fin.val_succ] at this
    exact Fin.ext (by omega)
  -- base points
  set pts : Fin q → ℂ := fun i => u (idx i) with hpts
  -- both `D` and `cmp` vanish at every `pts i`
  have hDz : ∀ i : Fin q, D (pts i) = 0 := fun i =>
    levelPTheta_frobDetCoeff_zero_at hp τ hτ u (idx i) (hidx_ne0 i)
  have hcmpz : ∀ i : Fin q, cmp (pts i) = 0 := fun i =>
    frobComparison_zero_at hp τ u (idx i) (hidx_ne0 i)
  -- membership in `𝒯_p^0(Ω) = 𝒯_{q+1}^0(Ω)`
  have hDmem : D ∈ ThetaSpace (q + 1) 0 ((p : ℂ) * τ) := by
    rw [← hpq]; exact levelPTheta_mem_ThetaSpace hp τ hτ _
  have hcmpmem : cmp ∈ ThetaSpace (q + 1) 0 ((p : ℂ) * τ) := by
    rw [← hpq]; exact frobComparison_mem_ThetaSpace hp τ hτ u
  -- `cmp ≠ 0` as a function
  have hcmpne : cmp ≠ 0 := by
    obtain ⟨w0, hw0⟩ := frobComparison_ne_zero_somewhere hp τ hτ u
    intro h
    exact hw0 (by have := congrFun h w0; simpa [hcmp] using this)
  -- DICHOTOMY: are the base points pairwise `deltaX`-nonzero?
  by_cases hdist : ∀ i j : Fin q, i ≠ j → deltaX ((p : ℂ) * τ) (pts i) (pts j) ≠ 0
  · -- distinct case: apply the general helper
    exact thetaSpace_proportional_of_shared_zeros hΩ q 0 D cmp hDmem hcmpmem hcmpne pts
      hdist hDz hcmpz
  · -- collision case: `D ≡ 0`, so `k = 0` works
    push_neg at hdist
    obtain ⟨i, j, hij, hδ0⟩ := hdist
    -- `deltaX Ω (pts i) (pts j) = 0 ↔ ∃ m n, pts j = pts i + m + n*Ω`
    rw [deltaX_zero_iff hΩ] at hδ0
    obtain ⟨m, n, hmn⟩ := hδ0
    -- so `u (idx j) - u (idx i) = m + n·(pτ)` — a `Λ_{pτ}`-coset collision between rows
    -- `idx j` and `idx i` (both `≠ 0`, hence untouched by the update at row `0`).
    have hcoset : u (idx j) - u (idx i) = (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ) := by
      have := hmn; simp only [hpts] at this; linear_combination this
    have hidxne : idx j ≠ idx i := fun h => hij (hidx_inj h).symm
    -- `D ≡ 0`: for every `w`, the updated matrix still has rows `idx j`, `idx i` on that coset.
    refine ⟨0, ?_⟩
    intro w
    rw [zero_mul]
    -- `D w = det (frobMatrix p τ (update u ⟨0,hp⟩ w))`
    have hDdet : D w = (frobMatrix p τ (Function.update u ⟨0, hp⟩ w)).det := by
      rw [hD]; exact (frobMatrix_det_update_eq_levelPTheta hp τ hτ u w).symm
    -- rewrite via `Fmat` (same entries) and apply the coset-vanishing theorem
    set v : Fin p → ℂ := Function.update u ⟨0, hp⟩ w with hv
    -- the two colliding rows are unchanged by the update (both indices `≠ 0`)
    have hvj : v (idx j) = u (idx j) := by
      rw [hv, Function.update_apply, if_neg (hidx_ne0 j)]
    have hvi : v (idx i) = u (idx i) := by
      rw [hv, Function.update_apply, if_neg (hidx_ne0 i)]
    have hcoset' : v (idx j) - v (idx i) = (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ) := by
      rw [hvj, hvi]; exact hcoset
    have hFrob_eq_Fmat : frobMatrix p τ v = ThetaDimension.Fmat τ p v := by
      funext r s
      simp only [frobMatrix, Matrix.of_apply, ThetaDimension.Fmat]
    have hdet0 : (frobMatrix p τ v).det = 0 := by
      rw [hFrob_eq_Fmat]
      exact ThetaDimension.Fmat_det_eq_zero_of_coset τ p v hidxne ⟨m, n, hcoset'⟩
    show D w = 0
    rw [hDdet, hdet0]
