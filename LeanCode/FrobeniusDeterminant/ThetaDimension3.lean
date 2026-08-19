import LeanCode.FrobeniusDeterminant.ThetaDimension2
import LeanCode.FrobeniusDeterminant.FrobeniusDeterminant
open Complex Topology Filter
namespace LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
open scoped Real
open LyubarskiiNes.TorsionJets

/-! ## Base case + dimension theorem -/

/-- Every `f ∈ 𝒯_1^α(T)` is a scalar multiple of `δ_{x(α)}`, `x(α)=α+(1+T)/2`. -/
theorem ThetaSpace_one_proportional {T α : ℂ} (hT : 0 < T.im) {f : ℂ → ℂ}
    (hf : f ∈ ThetaSpace 1 α T) :
    ∃ c : ℂ, ∀ z, f z = c * deltaX T (α + (1 + T) / 2) z := by
  have hvan : f (α + (1 + T) / 2) = 0 := ThetaSpace_one_vanishes hT hf
  obtain ⟨g, hga, hfac, hgmem⟩ := deltaX_div (N := 0) hT hf hvan
  have hgper1 : ∀ z, g (z + 1) = g z := hgmem.2.1
  have hgperT : ∀ z, g (z + T) = g z := by
    intro z
    have h := hgmem.2.2 z
    have haf : autFactor 0 (α - (α + (1 + T) / 2 - 1 / 2 - T / 2)) T z = 1 := by
      unfold autFactor; rw [show α - (α + (1 + T) / 2 - 1 / 2 - T / 2) = 0 by ring]; norm_num
    rwa [haf, one_mul] at h
  obtain ⟨c, hc⟩ := const_of_entire_doubly_periodic g (fun z => (hga z).differentiableAt) hT
    hgper1 hgperT
  exact ⟨c, fun z => by rw [hfac z, hc z, mul_comm]⟩

/-- `δ_{x(α)}` does not vanish at `x(α)+1/2` (since `1/2 ∉ ℤ+Tℤ`). -/
theorem deltaX_center_ne_at_half {T α : ℂ} (hT : 0 < T.im) :
    deltaX T (α + (1 + T) / 2) (α + (1 + T) / 2 + 1 / 2) ≠ 0 := by
  intro hz
  rw [deltaX_zero_iff hT] at hz
  obtain ⟨m, n, hmn⟩ := hz
  have h : (m : ℂ) + (n : ℂ) * T = 1 / 2 := by linear_combination -hmn
  have hn0 : n = 0 := by
    have him := congrArg Complex.im h
    have e1 : ((m : ℂ) + (n : ℂ) * T).im = (n : ℝ) * T.im := by
      simp [Complex.add_im, Complex.mul_im]
    have e2 : ((1 : ℂ) / 2).im = 0 := by norm_num
    rw [e1, e2] at him
    have := (mul_eq_zero.mp him).resolve_right hT.ne'
    exact_mod_cast this
  subst hn0
  simp only [Int.cast_zero, zero_mul, add_zero] at h
  have hre := congrArg Complex.re h
  rw [Complex.intCast_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num] at hre
  have h2 : 2 * m = 1 := by
    have : (2 : ℝ) * (m : ℝ) = 1 := by linarith [hre]
    exact_mod_cast this
  omega

/-- **H1 base-case input**: evaluation on `𝒯_1^α` is bijective at `x(α)+1/2`. -/
theorem thetaSpace_one_H1 {T : ℂ} (hT : 0 < T.im) (α : ℂ) :
    ∃ z₀ : ℂ, (∃ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ ≠ 0) ∧
      (∀ f : ThetaSpace (0+1) α T, (f : ℂ → ℂ) z₀ = 0 → f = 0) := by
  have hδmem : deltaX T (α + (1 + T) / 2) ∈ ThetaSpace 1 α T := by
    have := deltaX_mem_ThetaSpace hT (α + (1 + T) / 2)
    rwa [show α + (1 + T) / 2 - 1 / 2 - T / 2 = α by ring] at this
  have hδne : deltaX T (α + (1 + T) / 2) (α + (1 + T) / 2 + 1 / 2) ≠ 0 :=
    deltaX_center_ne_at_half hT
  refine ⟨α + (1 + T) / 2 + 1 / 2, ⟨⟨deltaX T (α + (1 + T) / 2), hδmem⟩, hδne⟩, ?_⟩
  intro f hfz
  obtain ⟨c, hc⟩ := ThetaSpace_one_proportional hT f.2
  have hcz : c * deltaX T (α + (1 + T) / 2) (α + (1 + T) / 2 + 1 / 2) = 0 := by
    rw [← hc]; exact hfz
  have hc0 : c = 0 := (mul_eq_zero.mp hcz).resolve_right hδne
  apply Subtype.ext; funext z
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [hc z, hc0, zero_mul]

/-- **Dimension theorem: `finrank ℂ 𝒯_N(α) = N` for `N ≥ 1`.** -/
theorem finrank_ThetaSpace {T : ℂ} (hT : 0 < T.im) (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    Module.finrank ℂ (ThetaSpace N α T) = N :=
  finrank_thetaSpace hT (thetaSpace_one_H1 hT) N hN α

theorem finiteDimensional_ThetaSpace {T : ℂ} (hT : 0 < T.im) (N : ℕ) (hN : 1 ≤ N) (α : ℂ) :
    FiniteDimensional ℂ (ThetaSpace N α T) :=
  finiteDimensional_thetaSpace hT (thetaSpace_one_H1 hT) N hN α

/-! ## Step (iii) machinery: DFT reduction + δ^k-division -/

theorem scaledDeriv_add {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    scaledDeriv (fun z => f z + g z) = fun z => scaledDeriv f z + scaledDeriv g z := by
  funext z
  have hd : deriv (fun w => f w + g w) z = deriv f z + deriv g z := deriv_add (hf z) (hg z)
  show paperDerivScale * deriv (fun w => f w + g w) z
    = paperDerivScale * deriv f z + paperDerivScale * deriv g z
  rw [hd]; ring

theorem iterScaledDeriv_zero (k : ℕ) : iterScaledDeriv k (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih => show scaledDeriv (iterScaledDeriv k (fun _ => 0)) = _
                 rw [ih]; funext z; show paperDerivScale * deriv (fun _ => (0:ℂ)) z = 0; simp

theorem iterScaledDeriv_add {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (k : ℕ) :
    iterScaledDeriv k (fun z => f z + g z)
      = fun z => iterScaledDeriv k f z + iterScaledDeriv k g z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show scaledDeriv (iterScaledDeriv k (fun z => f z + g z))
      = fun z => scaledDeriv (iterScaledDeriv k f) z + scaledDeriv (iterScaledDeriv k g) z
    rw [ih, scaledDeriv_add (diff_iterScaledDeriv hf k) (diff_iterScaledDeriv hg k)]

theorem iterScaledDeriv_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i)) (k : ℕ) :
    iterScaledDeriv k (fun z => ∑ i ∈ s, F i z)
      = fun z => ∑ i ∈ s, iterScaledDeriv k (F i) z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using iterScaledDeriv_zero k
  | @insert a s ha ih =>
    have hsumdiff : Differentiable ℂ (fun z => ∑ i ∈ s, F i z) :=
      Differentiable.fun_sum (fun i _ => hF i)
    have hrw : (fun z => ∑ i ∈ insert a s, F i z)
        = fun z => F a z + ∑ i ∈ s, F i z := by
      funext z; rw [Finset.sum_insert ha]
    rw [hrw, iterScaledDeriv_add (hF a) hsumdiff, ih]
    funext z; rw [Finset.sum_insert ha]

theorem polynomialScaledDeriv_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i)) (Q : Polynomial ℂ) (z : ℂ) :
    polynomialScaledDeriv Q (fun w => ∑ i ∈ s, F i w) z
      = ∑ i ∈ s, polynomialScaledDeriv Q (F i) z := by
  unfold polynomialScaledDeriv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [congrFun (iterScaledDeriv_finset_sum s F hF n) z, Finset.mul_sum]

theorem Phi_differentiable {q : ℕ} (hq : 0 < q) (r : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (Phi τ q r) :=
  fun z => (Phi_analyticAt hq r hτ z).differentiableAt

/-- `θ(·,τ) = ∑_{r<q} Φ_r`. -/
theorem theta_eq_sum_Phi {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiTheta₂ z τ = ∑ r : Fin q, Phi τ q ((r : ℕ) : ℤ) z := by
  have hsum : Summable (fun n : ℤ => jacobiTheta₂_term n z τ) := by
    have := summable_intpow_theta_term hτ z 0
    simpa using this
  rw [← (hasSum_jacobiTheta₂_term z hτ).tsum_eq,
    Regroup.tsum_int_regroup_mod hq hsum]
  rfl

/-- `Q(𝔡)θ = ∑_r Q(𝔡)Φ_r` pointwise. -/
theorem polynomialScaledDeriv_theta_sum {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im)
    (Q : Polynomial ℂ) (z : ℂ) :
    polynomialScaledDeriv Q (fun w => jacobiTheta₂ w τ) z
      = ∑ r : Fin q, polynomialScaledDeriv Q (Phi τ q ((r : ℕ) : ℤ)) z := by
  have heq : (fun w => jacobiTheta₂ w τ) = fun w => ∑ r : Fin q, Phi τ q ((r : ℕ) : ℤ) w := by
    funext w; exact theta_eq_sum_Phi hq hτ w
  rw [heq, polynomialScaledDeriv_finset_sum Finset.univ
    (fun r : Fin q => Phi τ q ((r : ℕ) : ℤ)) (fun r => Phi_differentiable hq _ hτ) Q z]

/-- Iterated shift: `Φ_r(z + s/q) = e^{2πirs/q}·Φ_r(z)`. -/
theorem Phi_shift_iter {q : ℕ} (r : ℤ) {τ : ℂ} (z : ℂ) (s : ℕ) :
    Phi τ q r (z + (s : ℂ) / (q : ℂ))
      = Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * (s : ℂ) / (q : ℂ)) * Phi τ q r z := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hstep : Phi τ q r (z + ((s : ℂ) + 1) / (q : ℂ))
        = Complex.exp (2 * ↑Real.pi * I * (r : ℂ) / (q : ℂ)) * Phi τ q r (z + (s : ℂ) / (q : ℂ)) := by
      rw [show z + ((s : ℂ) + 1) / (q : ℂ) = (z + (s : ℂ) / (q : ℂ)) + 1 / (q : ℂ) by ring]
      exact Phi_shift r (z + (s : ℂ) / (q : ℂ))
    rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, hstep, ih, ← mul_assoc,
      ← Complex.exp_add]
    congr 2
    · congr 1; ring

/-- `Q(𝔡)(C·f) = C·Q(𝔡)f`. -/
theorem polynomialScaledDeriv_const_mul_fun (C : ℂ) (Q : Polynomial ℂ) (f : ℂ → ℂ) (z : ℂ) :
    polynomialScaledDeriv Q (fun w => C * f w) z = C * polynomialScaledDeriv Q f z := by
  unfold polynomialScaledDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [iterScaledDeriv_const_mul C f n]; ring

/-- The operator jet of `Φ_r` at the torsion point picks up the phase `e^{2πirs/q}`. -/
theorem Phi_polyder_shift {q : ℕ} (r : ℤ) {τ : ℂ} (Q : Polynomial ℂ) (b : ℂ) (s : ℕ) :
    polynomialScaledDeriv Q (Phi τ q r) (b + (s : ℂ) / (q : ℂ))
      = Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * (s : ℂ) / (q : ℂ))
        * polynomialScaledDeriv Q (Phi τ q r) b := by
  rw [← polynomialScaledDeriv_comp_add Q (Phi τ q r) ((s : ℂ) / (q : ℂ)) b]
  have hfun : (fun w => Phi τ q r (w + (s : ℂ) / (q : ℂ)))
      = fun w => Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * (s : ℂ) / (q : ℂ)) * Phi τ q r w := by
    funext w; exact Phi_shift_iter r w s
  rw [hfun, polynomialScaledDeriv_const_mul_fun]

/-- **DFT reduction (step iii, part C):** if `Q(𝔡)θ` vanishes at all `q` torsion points `b+s/q`,
then each residue-jet `Q(𝔡)Φ_r(b)` vanishes. -/
theorem step3_dft {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im) (Q : Polynomial ℂ) (b : ℂ)
    (hvan : ∀ s : Fin q, polynomialScaledDeriv Q (fun w => jacobiTheta₂ w τ)
      (b + (s : ℕ) / (q : ℂ)) = 0) :
    ∀ r : Fin q, polynomialScaledDeriv Q (Phi τ q ((r : ℕ) : ℤ)) b = 0 := by
  apply dft_inversion hq (fun r : Fin q => polynomialScaledDeriv Q (Phi τ q ((r : ℕ) : ℤ)) b)
  intro s
  have key : polynomialScaledDeriv Q (fun w => jacobiTheta₂ w τ) (b + (s : ℕ) / (q : ℂ))
      = ∑ r : Fin q, polynomialScaledDeriv Q (Phi τ q ((r : ℕ) : ℤ)) b
          * Complex.exp (2 * ↑Real.pi * I * (r : ℕ) * ((s : ℕ) / (q : ℂ))) := by
    rw [polynomialScaledDeriv_theta_sum hq hτ]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Phi_polyder_shift ((r : ℕ) : ℤ) Q b (s : ℕ), mul_comm]
    congr 2
    push_cast; ring
  rw [← key]; exact hvan s

/-! ## Leading-coefficient machinery (order↔jet bridge, existence-at-b, δ^d membership) -/

theorem paperDerivScale_ne_zero : (paperDerivScale : ℂ) ≠ 0 := by
  unfold paperDerivScale
  simp [Real.pi_ne_zero, Complex.I_ne_zero, two_ne_zero]

theorem iteratedDeriv_analyticAt {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) :
    ∀ (n : ℕ) (z : ℂ), AnalyticAt ℂ (iteratedDeriv n f) z := by
  intro n
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih => intro z; rw [iteratedDeriv_succ]; exact (ih z).deriv

theorem iterScaledDeriv_eq_pow_iteratedDeriv {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (k : ℕ)
    (z : ℂ) :
    iterScaledDeriv k f z = paperDerivScale ^ k * iteratedDeriv k f z := by
  induction k generalizing z with
  | zero => simp [iterScaledDeriv, iteratedDeriv_zero]
  | succ k ih =>
    have hdiff : Differentiable ℂ (iteratedDeriv k f) :=
      fun z => (iteratedDeriv_analyticAt hf k z).differentiableAt
    show scaledDeriv (iterScaledDeriv k f) z = paperDerivScale ^ (k+1) * iteratedDeriv (k+1) f z
    have hfun : iterScaledDeriv k f = fun w => paperDerivScale ^ k * iteratedDeriv k f w := by
      funext w; exact ih w
    rw [show scaledDeriv (iterScaledDeriv k f) z = paperDerivScale * deriv (iterScaledDeriv k f) z from rfl,
      hfun, deriv_const_mul _ (hdiff z), iteratedDeriv_succ, pow_succ]
    ring

/-- For `M' ≥ 1`, some element of `𝒯_{M'+1}^γ(T)` is nonzero at any given `b`. -/
theorem exists_ne_at {T : ℂ} (hT : 0 < T.im) (M' : ℕ) (hM' : 1 ≤ M') (γ b : ℂ) :
    ∃ f : ℂ → ℂ, f ∈ ThetaSpace (M' + 1) γ T ∧ f b ≠ 0 := by
  by_contra h
  push_neg at h
  have hev0 : evAt M' γ T b = 0 := by
    ext f
    show (f : ℂ → ℂ) b = 0
    exact h f f.2
  have hkertop : LinearMap.ker (evAt M' γ T b) = ⊤ := by
    rw [LinearMap.ker_eq_top]; exact hev0
  haveI : FiniteDimensional ℂ (ThetaSpace M' (γ - (b - 1/2 - T/2)) T) :=
    finiteDimensional_ThetaSpace hT M' hM' _
  have h1 : Module.finrank ℂ (LinearMap.ker (evAt M' γ T b)) = M' := by
    rw [← (kerEvEquiv hT M' γ b).finrank_eq, finrank_ThetaSpace hT M' hM']
  have h2 : Module.finrank ℂ (LinearMap.ker (evAt M' γ T b))
      = Module.finrank ℂ (ThetaSpace (M' + 1) γ T) := by
    rw [hkertop]; exact finrank_top ℂ _
  rw [h2, finrank_ThetaSpace hT (M' + 1) (by omega)] at h1
  omega

/-- `δ_b^d ∈ 𝒯_d^{d·β_b}(T)`. -/
theorem deltaX_pow_mem {T : ℂ} (hT : 0 < T.im) (b : ℂ) (d : ℕ) :
    (fun z => (deltaX T b z) ^ d) ∈ ThetaSpace d ((d : ℂ) * (b - 1/2 - T/2)) T := by
  induction d with
  | zero =>
    refine ⟨fun z => analyticAt_const, fun z => by simp, fun z => ?_⟩
    simp only [pow_zero]
    rw [show autFactor 0 ((0:ℕ) * (b - 1/2 - T/2)) T z = 1 by
      unfold autFactor; push_cast; simp]
    ring
  | succ d ih =>
    have hδ : deltaX T b ∈ ThetaSpace 1 (b - 1/2 - T/2) T := by
      have := deltaX_mem_ThetaSpace hT b; simpa using this
    have hmul := ThetaSpace_mul hδ ih
    have hfun : (fun z => deltaX T b z * (deltaX T b z) ^ d) = fun z => (deltaX T b z) ^ (d + 1) := by
      funext z; rw [← pow_succ']
    have hchar : (b - 1/2 - T/2) + (d : ℂ) * (b - 1/2 - T/2)
        = ((d + 1 : ℕ) : ℂ) * (b - 1/2 - T/2) := by push_cast; ring
    rw [hfun, show (1 + d) = (d + 1) by omega, hchar] at hmul
    exact hmul

/-! ## Step (iii): residue-jet independence (F4 core) -/

theorem polynomialScaledDeriv_add_fun {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (Q : Polynomial ℂ) (z : ℂ) :
    polynomialScaledDeriv Q (fun w => f w + g w) z
      = polynomialScaledDeriv Q f z + polynomialScaledDeriv Q g z := by
  unfold polynomialScaledDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [congrFun (iterScaledDeriv_add hf hg n) z]; ring

/-- Evaluation functional `f ↦ Q(𝔡)f(b)` on `𝒯_q^0(qτ)`. -/
noncomputable def polyEval (q : ℕ) (τ b : ℂ) (Q : Polynomial ℂ) :
    ThetaSpace q 0 ((q : ℂ) * τ) →ₗ[ℂ] ℂ where
  toFun f := polynomialScaledDeriv Q (f : ℂ → ℂ) b
  map_add' f g := by
    show polynomialScaledDeriv Q (fun w => (f : ℂ → ℂ) w + (g : ℂ → ℂ) w) b = _
    exact polynomialScaledDeriv_add_fun (fun z => (f.2.1 z).differentiableAt)
      (fun z => (g.2.1 z).differentiableAt) Q b
  map_smul' c f := by
    show polynomialScaledDeriv Q (fun w => c * (f : ℂ → ℂ) w) b = c * polynomialScaledDeriv Q _ b
    exact polynomialScaledDeriv_const_mul_fun c Q _ b

/-- The `Φ_r` (as elements of `𝒯_q^0(qτ)`) are linearly independent. -/
theorem Phi_linearIndependent {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im) :
    LinearIndependent ℂ (fun r : Fin q =>
      (⟨Phi τ q ((r : ℕ) : ℤ), Phi_mem hq _ hτ⟩ : ThetaSpace q 0 ((q : ℂ) * τ))) := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum r
  have hfun : ∀ z, ∑ r : Fin q, a r * Phi τ q ((r : ℕ) : ℤ) z = 0 := by
    intro z
    have h := congrArg (fun (f : ThetaSpace q 0 ((q : ℂ) * τ)) => (f : ℂ → ℂ) z) hsum
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, Submodule.coe_sum, SetLike.val_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  exact Phi_indep hτ hq a hfun r

theorem qtau_im_pos {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im) : 0 < ((q : ℂ) * τ).im := by
  rw [Complex.mul_im, Complex.natCast_im, Complex.natCast_re, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hq) hτ

/-- **`Q(𝔡)f(b)=0` for every `f ∈ 𝒯_q^0(qτ)`** (from vanishing on the `Φ_r` basis). -/
theorem polyEval_eq_zero {q : ℕ} (hq : 0 < q) {τ : ℂ} (hτ : 0 < τ.im) (b : ℂ) (Q : Polynomial ℂ)
    (hΦ : ∀ r : Fin q, polynomialScaledDeriv Q (Phi τ q ((r : ℕ) : ℤ)) b = 0) :
    polyEval q τ b Q = 0 := by
  haveI : FiniteDimensional ℂ (ThetaSpace q 0 ((q : ℂ) * τ)) :=
    finiteDimensional_ThetaSpace (qtau_im_pos hq hτ) q (by omega) 0
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hspan : Submodule.span ℂ (Set.range (fun r : Fin q =>
      (⟨Phi τ q ((r : ℕ) : ℤ), Phi_mem hq _ hτ⟩ : ThetaSpace q 0 ((q : ℂ) * τ)))) = ⊤ :=
    (Phi_linearIndependent hq hτ).span_eq_top_of_card_eq_finrank (by
      rw [Fintype.card_fin, finrank_ThetaSpace (qtau_im_pos hq hτ) q (by omega)])
  ext f
  have hfmem : f ∈ Submodule.span ℂ (Set.range (fun r : Fin q =>
      (⟨Phi τ q ((r : ℕ) : ℤ), Phi_mem hq _ hτ⟩ : ThetaSpace q 0 ((q : ℂ) * τ)))) :=
    hspan ▸ Submodule.mem_top
  induction hfmem using Submodule.span_induction with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact hΦ r
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, hx, smul_zero]

/-- If the lower scaled-derivative jets vanish, `Q(𝔡)e(b)` picks out the leading coefficient. -/
theorem polyScaledDeriv_leading {e : ℂ → ℂ} {Q : Polynomial ℂ} {d : ℕ} (b : ℂ)
    (hd : Q.natDegree = d) (hjet : ∀ k, k < d → iterScaledDeriv k e b = 0) :
    polynomialScaledDeriv Q e b = Q.coeff d * iterScaledDeriv d e b := by
  unfold polynomialScaledDeriv
  rw [Finset.sum_eq_single d]
  · intro k hk hkd
    have hle : k ≤ d := hd ▸ Polynomial.le_natDegree_of_mem_supp k hk
    rw [hjet k (lt_of_le_of_ne hle hkd), mul_zero]
  · intro hnotin
    have hc0 : Q.coeff d = 0 := by
      by_contra h; exact hnotin (Polynomial.mem_support_iff.mpr h)
    rw [hc0, zero_mul]

/-- At a point of analytic order exactly `d`, the `d`-th scaled derivative is nonzero. -/
theorem iterScaledDeriv_at_order_ne {e : ℂ → ℂ} (he : ∀ z, AnalyticAt ℂ e z) {d : ℕ} {b : ℂ}
    (hord : analyticOrderAt e b = (d : ℕ∞)) : iterScaledDeriv d e b ≠ 0 := by
  rw [iterScaledDeriv_eq_pow_iteratedDeriv he d b]
  refine mul_ne_zero (pow_ne_zero d paperDerivScale_ne_zero) ?_
  intro hzero
  have hge : ((d + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt e b := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (he b)]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (he b)).mp
        (le_of_eq hord.symm) i h
    · rw [h]; exact hzero
  rw [hord] at hge
  exact absurd (Nat.cast_le.mp hge) (by omega)

/-- **Step (iii) — residue-jet independence for `θ(·,τ)`.**  A nonzero `Q` of degree `≤ q-2` cannot
make `Q(𝔡)θ` vanish at all `q` torsion points `b + s/q`. -/
theorem thetaTorsionJetIndep {q : ℕ} (hq2 : 2 ≤ q) {τ : ℂ} (hτ : 0 < τ.im) (b : ℂ)
    {Q : Polynomial ℂ} (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ q - 2)
    (hvan : ∀ s : Fin q, polynomialScaledDeriv Q (fun w => jacobiTheta₂ w τ)
      (b + (s : ℕ) / (q : ℂ)) = 0) : False := by
  have hq : 0 < q := by omega
  set T := (q : ℂ) * τ with hTdef
  have hT : 0 < T.im := qtau_im_pos hq hτ
  set β := b - 1 / 2 - T / 2 with hβdef
  obtain ⟨g, hgmem, hgb⟩ := exists_ne_at hT (q - Q.natDegree - 1) (by omega) (-(Q.natDegree : ℂ) * β) b
  rw [show (q - Q.natDegree - 1) + 1 = q - Q.natDegree by omega] at hgmem
  set e := fun z => (deltaX T b z) ^ Q.natDegree * g z with hedef
  have hea : ∀ z, AnalyticAt ℂ e z := fun z => ((deltaX_analyticAt hT b z).pow _).mul (hgmem.1 z)
  have hemem : e ∈ ThetaSpace q 0 T := by
    have hmul := ThetaSpace_mul (deltaX_pow_mem hT b Q.natDegree) hgmem
    rw [show Q.natDegree + (q - Q.natDegree) = q by omega,
      show (Q.natDegree : ℂ) * β + -(Q.natDegree : ℂ) * β = 0 by ring] at hmul
    exact hmul
  have hord : analyticOrderAt e b = (Q.natDegree : ℕ∞) := deltaXpow_mul_order hT b _ hgmem.1 hgb
  have hjet : ∀ k, k < Q.natDegree → iterScaledDeriv k e b = 0 := by
    intro k hk
    rw [iterScaledDeriv_eq_pow_iteratedDeriv hea k b,
      deltaXpow_mul_iteratedDeriv_eq_zero hT b Q.natDegree hgmem.1 hgb k hk, mul_zero]
  have hEval0 : polynomialScaledDeriv Q e b = 0 := by
    have h0 := polyEval_eq_zero hq hτ b Q (step3_dft hq hτ Q b hvan)
    have h2 := LinearMap.congr_fun h0 ⟨e, hemem⟩
    simpa [polyEval] using h2
  rw [polyScaledDeriv_leading b rfl hjet] at hEval0
  have hlc : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  exact (mul_ne_zero hlc (iterScaledDeriv_at_order_ne hea hord)) hEval0

/-! ## F3 foundations: θ quasi-period, column basis, Frobenius coset row-vanishing -/

theorem jacobiTheta₂_add_intMul_tau (τ w : ℂ) (M : ℤ) :
    jacobiTheta₂ (w + (M : ℂ) * τ) τ
      = Complex.exp (-π * I * ((M : ℂ)^2 * τ + 2 * (M : ℂ) * w)) * jacobiTheta₂ w τ := by
  induction M using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have e : w + (((k : ℤ) + 1 : ℤ) : ℂ) * τ = (w + ((k : ℤ) : ℂ) * τ) + τ := by
        push_cast; ring
      rw [e, jacobiTheta₂_add_left', ih]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast; ring_nf
  | pred k ih =>
      have e : w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * τ = (w + (-(k : ℂ)) * τ) - τ := by
        push_cast; ring
      rw [e]
      have h0 := jacobiTheta₂_add_left' ((w + (-(k : ℂ)) * τ) - τ) τ
      rw [show ((w + (-(k : ℂ)) * τ) - τ) + τ = w + (-(k : ℂ)) * τ from by ring] at h0
      have ihk : jacobiTheta₂ (w + (-(k : ℂ)) * τ) τ
          = Complex.exp (-↑π * I * ((-(k : ℂ))^2 * τ + 2 * (-(k : ℂ)) * w)) * jacobiTheta₂ w τ := by
        have := ih; push_cast at this ⊢; convert this using 3
      rw [ihk] at h0
      have key : jacobiTheta₂ ((w + (-(k : ℂ)) * τ) - τ) τ
          = Complex.exp (-(-↑π * I * (τ + 2 * ((w + (-(k : ℂ)) * τ) - τ))))
              * (Complex.exp (-↑π * I * ((-(k : ℂ))^2 * τ + 2 * (-(k : ℂ)) * w)) * jacobiTheta₂ w τ) := by
        rw [h0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
      rw [key, ← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast; ring

/-- The `s`-th primitive theta column: `z ↦ θ(z + s/p, τ)`. -/
noncomputable def thetaCol (τ : ℂ) (p : ℕ) (s : ℕ) (z : ℂ) : ℂ :=
    jacobiTheta₂ (z + (s : ℂ) / (p : ℂ)) τ

/-- **Target 2 — the DFT relation.**
`thetaCol τ p s` is the discrete Fourier transform of the `Φ`-basis:
`θ(z + s/p) = ∑_r exp(2πi r s / p) · Φ_r(z)`. -/
theorem thetaCol_eq_sum_Phi {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) (s : ℕ) (z : ℂ) :
    thetaCol τ p s z
      = ∑ r : Fin p,
          Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * (s : ℂ) / (p : ℂ)) * Phi τ p ((r : ℕ) : ℤ) z := by
  unfold thetaCol
  rw [theta_eq_sum_Phi hp hτ (z + (s : ℂ) / (p : ℂ))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Phi_shift_iter ((r : ℕ) : ℤ) z s]
  push_cast
  ring

/-- **Target 1 — membership.**
`thetaCol τ p s ∈ 𝒯_p^0(pτ)`, obtained as a linear combination of the `Φ_r ∈ 𝒯_p^0(pτ)`. -/
theorem thetaCol_mem {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) (s : ℕ) :
    thetaCol τ p s ∈ ThetaSpace p 0 ((p : ℂ) * τ) := by
  -- thetaCol = ∑_r c_r • Φ_r, a finite ℂ-combination of members of the submodule.
  have hfun : (thetaCol τ p s)
      = ∑ r : Fin p,
          (Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * (s : ℂ) / (p : ℂ)))
            • (Phi τ p ((r : ℕ) : ℤ)) := by
    funext z
    rw [thetaCol_eq_sum_Phi hp hτ s z]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.sum_mem _ (fun r _ =>
    Submodule.smul_mem _ _ (Phi_mem hp ((r : ℕ) : ℤ) hτ))

/-- Packaged element of the theta space. -/
noncomputable def thetaColElt {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) (s : Fin p) :
    ThetaSpace p 0 ((p : ℂ) * τ) :=
  ⟨thetaCol τ p (s : ℕ), thetaCol_mem hp hτ (s : ℕ)⟩

/-- **Target 3 — linear independence of the primitive theta columns.**
The family `(fun s : Fin p => thetaColElt hp hτ s)` is `ℂ`-linearly independent in `𝒯_p^0(pτ)`.
Proof: `thetaCol` is the DFT of the linearly independent `Φ`-basis, and the DFT is invertible. -/
theorem thetaCol_linearIndependent {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) :
    LinearIndependent ℂ (fun s : Fin p => thetaColElt hp hτ s) := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum s
  -- unfold the vanishing combination to a pointwise statement on functions
  have hfun : ∀ z : ℂ, ∑ t : Fin p, a t * thetaCol τ p ((t : ℕ)) z = 0 := by
    intro z
    have h := congrArg (fun (f : ThetaSpace p 0 ((p : ℂ) * τ)) => (f : ℂ → ℂ) z) hsum
    rw [Submodule.coe_zero, Pi.zero_apply] at h
    rw [← h]
    rw [AddSubmonoid.coe_finsetSum]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Submodule.coe_smul_of_tower]
    simp only [thetaColElt, Pi.smul_apply, smul_eq_mul]
  -- expand each column as its DFT and regroup by residue r
  have hregroup : ∀ z : ℂ,
      ∑ r : Fin p,
        (∑ t : Fin p, a t * Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((t : ℕ) : ℂ) / (p : ℂ)))
          * Phi τ p ((r : ℕ) : ℤ) z = 0 := by
    intro z
    rw [← hfun z]
    -- RHS ∑_t a_t thetaCol_t = ∑_t a_t ∑_r c_{r,t} Phi_r = ∑_r (∑_t a_t c_{r,t}) Phi_r
    have hrhs : ∀ t : Fin p, a t * thetaCol τ p ((t : ℕ)) z
        = ∑ r : Fin p,
            a t * Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((t : ℕ) : ℂ) / (p : ℂ))
              * Phi τ p ((r : ℕ) : ℤ) z := by
      intro t
      rw [thetaCol_eq_sum_Phi hp hτ (t : ℕ) z, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun t _ => hrhs t), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul]
  -- Φ-independence kills each inner coefficient
  have hcoeff : ∀ r : Fin p,
      (∑ t : Fin p, a t * Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((t : ℕ) : ℂ) / (p : ℂ))) = 0 := by
    have := Phi_indep hτ hp
      (fun r : Fin p =>
        ∑ t : Fin p, a t * Complex.exp (2 * ↑Real.pi * I * (r : ℂ) * ((t : ℕ) : ℂ) / (p : ℂ)))
      (by
        intro z
        have := hregroup z
        simpa using this)
    exact this
  -- the inner coefficient is exactly a DFT; invert it
  refine dft_inversion hp a ?_ s
  intro r
  have h := hcoeff r
  rw [← h]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1
  rw [mul_div_assoc]
  congr 1
  ring

/-- The Frobenius theta matrix: rows indexed by `r`, columns by `s`, entry
`θ(u r + s/p, τ)`. -/
noncomputable def Fmat (τ : ℂ) (p : ℕ) (u : Fin p → ℂ) :
    Matrix (Fin p) (Fin p) ℂ :=
  fun r s => jacobiTheta₂ (u r + (s : ℂ) / (p : ℂ)) τ

/-- **Row proportionality from a common `Λ_{pτ}`-coset.**  If `u a` and `u b`
differ by a lattice vector `m + n·(pτ)`, then row `a` equals a constant
(`s`-independent) scalar times row `b`. -/
theorem Fmat_row_eq_smul_row (τ : ℂ) (p : ℕ) (u : Fin p → ℂ)
    {a b : Fin p} (m n : ℤ)
    (huab : u a - u b = (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ)) :
    ∀ s : Fin p,
      Fmat τ p u a s
        = Complex.exp (-π * I * (((n * (p : ℤ) : ℤ) : ℂ)^2 * τ
              + 2 * ((n * (p : ℤ) : ℤ) : ℂ) * (u b))) * Fmat τ p u b s := by
  intro s
  simp only [Fmat]
  -- u a = u b + m + n*(p*τ)
  have hua : u a = u b + (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ) := by
    have := huab; linear_combination this
  set w := u b + (s : ℂ) / (p : ℂ) with hw
  -- rewrite argument of row a
  have harg : u a + (s : ℂ) / (p : ℂ)
      = (w + ((n * (p : ℤ) : ℤ) : ℂ) * τ) + (m : ℂ) := by
    rw [hua, hw]; push_cast; ring
  rw [harg, ThetaZeroCount.jacobiTheta₂_add_intCast, jacobiTheta₂_add_intMul_tau]
  -- now factor exp(-πi(M²τ + 2 M w)), M = n*p, w = u b + s/p.
  -- Need to split off the s-dependent part: 2 M w = 2 M (u b) + 2 M (s/p),
  -- and exp(-πi·2 M (s/p)) = exp(-2πi n s) = 1 since M/p = n, s integer.
  congr 1
  -- reduce exp(-πi(M²τ + 2 M w)) = exp(-πi(M²τ + 2 M u b))
  rw [hw]
  have hp : (p : ℂ) ≠ 0 := by
    have : 0 < p := Fin.pos s
    exact_mod_cast this.ne'
  set M : ℂ := ((n * (p : ℤ) : ℤ) : ℂ) with hM
  have hsplit : -↑π * I * (M^2 * τ + 2 * M * (u b + (s : ℂ) / (p : ℂ)))
      = (-↑π * I * (M^2 * τ + 2 * M * (u b))) + (-(2 * ↑π * I) * ((n : ℂ) * (s : ℂ))) := by
    rw [hM]; field_simp; push_cast; ring
  rw [hsplit, Complex.exp_add]
  -- exp(-(2πi)(n s)) = 1
  have hns : (-(2 * ↑π * I) * ((n : ℂ) * (s : ℂ)))
      = (↑(-(n * (s : ℕ)) : ℤ) : ℂ) * (2 * ↑π * I) := by
    push_cast; ring
  rw [hns, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **TARGET.**  Two rows of the Frobenius theta matrix on the same `Λ_{pτ}`-coset
force the determinant to vanish. -/
theorem Fmat_det_eq_zero_of_coset (τ : ℂ) (p : ℕ) (u : Fin p → ℂ)
    {a b : Fin p} (hab : a ≠ b)
    (h : ∃ (m n : ℤ), u a - u b = (m : ℂ) + (n : ℂ) * ((p : ℂ) * τ)) :
    (Fmat τ p u).det = 0 := by
  obtain ⟨m, n, huab⟩ := h
  exact det_eq_zero_of_row_eq_smul_row (Fmat τ p u) hab
    (Complex.exp (-π * I * (((n * (p : ℤ) : ℤ) : ℂ)^2 * τ
        + 2 * ((n * (p : ℤ) : ℤ) : ℂ) * (u b))))
    (Fmat_row_eq_smul_row τ p u m n huab)

end LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
