import LeanCode.GeneralLattice.GeneralizedRank

open scoped BigOperators Matrix

namespace LyubarskiiNes.GeneralLattice

lemma continuous_generalizedZakModularArg (γ : ℝ) (τ : ℂ) :
    Continuous fun z : ℝ × ℝ => generalizedZakModularArg γ τ z.1 z.2 := by
  unfold generalizedZakModularArg generalizedZakArg generalizedZakTau
  continuity

lemma continuous_generalizedZakModularTheta
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) :
    Continuous fun z : ℝ × ℝ =>
      jacobiTheta₂ (generalizedZakModularArg γ τ z.1 z.2)
        (generalizedZakModularTau γ τ) := by
  have harg := continuous_generalizedZakModularArg γ τ
  have hpair : Continuous fun z : ℝ × ℝ =>
      (generalizedZakModularArg γ τ z.1 z.2, generalizedZakModularTau γ τ) :=
    harg.prodMk continuous_const
  rw [continuous_iff_continuousAt]
  intro z
  exact ContinuousAt.comp (x := z)
    (continuousAt_jacobiTheta₂ _ (generalizedZakModularTau_im_pos hγ hτ))
    hpair.continuousAt

lemma continuous_generalizedZakModularTheta_deriv
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) :
    Continuous fun z : ℝ × ℝ =>
      jacobiTheta₂' (generalizedZakModularArg γ τ z.1 z.2)
        (generalizedZakModularTau γ τ) := by
  have harg := continuous_generalizedZakModularArg γ τ
  have hpair : Continuous fun z : ℝ × ℝ =>
      (generalizedZakModularArg γ τ z.1 z.2, generalizedZakModularTau γ τ) :=
    harg.prodMk continuous_const
  rw [continuous_iff_continuousAt]
  intro z
  exact ContinuousAt.comp (x := z)
    (continuousAt_jacobiTheta₂' _ (generalizedZakModularTau_im_pos hγ hτ))
    hpair.continuousAt

/-- Joint continuity of the modular closed generalized Zak formula. -/
theorem continuous_generalizedZakH1ModularClosedForm
    {γ : ℝ} {τ : ℂ} (hγ : γ ≠ 0) (hτ : 0 < τ.im) :
    Continuous fun z : ℝ × ℝ => generalizedZakH1ModularClosedForm γ τ z.1 z.2 := by
  have htheta := continuous_generalizedZakModularTheta hγ hτ
  have htheta' := continuous_generalizedZakModularTheta_deriv hγ hτ
  unfold generalizedZakH1ModularClosedForm generalizedZakArg generalizedZakTau
    generalizedZakModularArg generalizedZakModularTau
  continuity

/-- Continuity of the canonical generalized rational Zak matrix. -/
theorem continuous_generalizedCanonicalZakPMatrix
    {p q : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) :
    Continuous (generalizedCanonicalZakPMatrix τ p q) := by
  apply continuous_matrix
  intro s t
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hbase := continuous_generalizedZakH1ModularClosedForm
    (γ := (p : ℝ)) (τ := τ) hpR hτ
  have hmap : Continuous fun z : ℝ × ℝ =>
      (z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ), z.2) := by
    continuity
  have hcomp := hbase.comp hmap
  apply hcomp.congr
  intro z
  unfold generalizedCanonicalZakPMatrix
  exact (generalizedZakH1_modular_formula hpR hτ _ _).symm

lemma generalizedCanonicalZakPMatrix_freq_period
    {p q : ℕ} (hp : 0 < p) (τ : ℂ) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    generalizedCanonicalZakPMatrix τ p q (z.1, z.2 + (p : ℝ)⁻¹) s t =
      generalizedCanonicalZakPMatrix τ p q z s t := by
  unfold generalizedCanonicalZakPMatrix
  exact Zak.zakTransform_freq_period (by exact_mod_cast Nat.ne_of_gt hp)
    (generalizedH1 τ) _ _

lemma generalizedCanonicalZakPMatrix_add_period
    (p q : ℕ) (τ : ℂ) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    generalizedCanonicalZakPMatrix τ p q (z.1 + (p : ℝ), z.2) s t =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (z.2 : ℂ)) *
        generalizedCanonicalZakPMatrix τ p q z s t := by
  unfold generalizedCanonicalZakPMatrix
  let y : ℝ := z.1 + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ)
  have hy :
      (z.1 + (p : ℝ)) + (p : ℝ) * ((t : ℕ) : ℝ) / (q : ℝ) + ((s : ℕ) : ℝ) =
        y + (p : ℝ) := by
    dsimp [y]
    ring
  rw [hy]
  exact Zak.zakTransform_add_period (p : ℝ) (generalizedH1 τ) y z.2

private lemma norm_canonical_spatial_phase (p : ℕ) (y : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (y : ℂ))‖ = 1 := by
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (y : ℂ) =
        ((2 * Real.pi * (p : ℝ) * y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

lemma generalizedCanonicalZakPMatrix_norm_add_period
    (p q : ℕ) (τ : ℂ) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    ‖generalizedCanonicalZakPMatrix τ p q (z.1 + (p : ℝ), z.2) s t‖ =
      ‖generalizedCanonicalZakPMatrix τ p q z s t‖ := by
  rw [generalizedCanonicalZakPMatrix_add_period]
  rw [norm_mul, norm_canonical_spatial_phase, one_mul]

lemma generalizedCanonicalZakPMatrix_norm_freq_period
    {p q : ℕ} (hp : 0 < p) (τ : ℂ) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    ‖generalizedCanonicalZakPMatrix τ p q (z.1, z.2 + (p : ℝ)⁻¹) s t‖ =
      ‖generalizedCanonicalZakPMatrix τ p q z s t‖ := by
  rw [generalizedCanonicalZakPMatrix_freq_period hp]

lemma generalizedCanonicalZakMatrix_mulVec_norm_freq_period
    {p q : ℕ} (hp : 0 < p) (τ : ℂ) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖generalizedCanonicalZakMatrix τ p q (z.1, z.2 + (p : ℝ)⁻¹) *ᵥ w‖ =
      ‖generalizedCanonicalZakMatrix τ p q z *ᵥ w‖ := by
  have hP : generalizedCanonicalZakPMatrix τ p q (z.1, z.2 + (p : ℝ)⁻¹) =
      generalizedCanonicalZakPMatrix τ p q z := by
    ext s t
    exact generalizedCanonicalZakPMatrix_freq_period hp τ z s t
  unfold generalizedCanonicalZakMatrix
  rw [hP]

lemma generalizedCanonicalZakMatrix_mulVec_norm_add_period
    (p q : ℕ) (τ : ℂ) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖generalizedCanonicalZakMatrix τ p q (z.1 + (p : ℝ), z.2) *ᵥ w‖ =
      ‖generalizedCanonicalZakMatrix τ p q z *ᵥ w‖ := by
  let c : ℂ := Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (z.2 : ℂ))
  have hc : ‖star c‖ = 1 := by simpa [c] using norm_canonical_spatial_phase p z.2
  have hvec :
      generalizedCanonicalZakMatrix τ p q (z.1 + (p : ℝ), z.2) *ᵥ w =
        (star c) • (generalizedCanonicalZakMatrix τ p q z *ᵥ w) := by
    ext i
    dsimp [c]
    simp [Matrix.mulVec, dotProduct, generalizedCanonicalZakMatrix,
      generalizedCanonicalZakPMatrix_add_period, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [hvec, norm_smul, hc, one_mul]

/-- Uniform positive lower and finite upper matrix bounds for the generalized
canonical Zak matrix. -/
theorem generalizedCanonicalZakMatrix_uniform_bounds
    {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hpq_coprime : Nat.Coprime p q) (hgap : q ≥ p + 2)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      (∀ z w, A * ‖w‖ ^ 2 ≤ ‖generalizedCanonicalZakMatrix τ p q z *ᵥ w‖ ^ 2) ∧
      (∀ z w, ‖generalizedCanonicalZakMatrix τ p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2) := by
  have hPcont := continuous_generalizedCanonicalZakPMatrix
    (p := p) (q := q) (τ := τ) hp hτ
  have hMcont : Continuous (generalizedCanonicalZakMatrix τ p q) :=
    LyubarskiiNes.RationalDensity.continuous_conjTranspose_matrix_field hPcont
  have hinj := generalizedCanonicalZakMatrix_injective hp hpq_coprime hgap hτ
  rcases LyubarskiiNes.RationalDensity.exists_uniform_lower_bound_of_continuous_periodic_injective
      (M := generalizedCanonicalZakMatrix τ p q)
      (a := (p : ℝ)) (b := (p : ℝ)⁻¹)
      (by exact_mod_cast hp) (inv_pos.mpr (by exact_mod_cast hp)) hMcont
      (generalizedCanonicalZakMatrix_mulVec_norm_add_period p q τ)
      (generalizedCanonicalZakMatrix_mulVec_norm_freq_period hp τ)
      hinj (LyubarskiiNes.RationalDensity.fin_complex_unit_sphere_nonempty hp) with
    ⟨A, hA, hlower⟩
  have hentryP : ∀ i j, ∃ Cij : ℝ, ∀ z,
      ‖generalizedCanonicalZakPMatrix τ p q z i j‖ ≤ Cij := by
    intro i j
    have hc : Continuous fun z : ℝ × ℝ => generalizedCanonicalZakPMatrix τ p q z i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hPcont)
    exact LyubarskiiNes.RationalDensity.exists_norm_bound_of_continuous_norm_periodic_prod
      (by exact_mod_cast hp) (inv_pos.mpr (by exact_mod_cast hp)) hc
      (generalizedCanonicalZakPMatrix_norm_add_period p q τ · i j)
      (generalizedCanonicalZakPMatrix_norm_freq_period hp τ · i j)
  have hentryM : ∀ i j, ∃ Cij : ℝ, ∀ z,
      ‖generalizedCanonicalZakMatrix τ p q z i j‖ ≤ Cij :=
    LyubarskiiNes.RationalDensity.conjTranspose_matrix_field_entries_bounded hentryP
  choose Cij hCij using hentryM
  let C : ℝ := ∑ i : Fin q, ∑ j : Fin p, max 0 (Cij i j)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_left _ _
  have hentry : ∀ z i j, ‖generalizedCanonicalZakMatrix τ p q z i j‖ ≤ C := by
    intro z i j
    have hj : max 0 (Cij i j) ≤ ∑ j' : Fin p, max 0 (Cij i j') :=
      Finset.single_le_sum (fun _ _ => le_max_left 0 _) (Finset.mem_univ j)
    have hi : (∑ j' : Fin p, max 0 (Cij i j')) ≤ C := by
      exact Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ => le_max_left 0 (Cij i' j'))
        (Finset.mem_univ i)
    exact le_trans (hCij i j z) (le_trans (le_max_right 0 _) (le_trans hj hi))
  rcases LyubarskiiNes.RationalDensity.rationalZakMatrix_uniform_upper_bound_of_entry_bound
      (generalizedCanonicalZakMatrix τ p q) hC hentry with ⟨B₀, hB₀, hupper⟩
  refine ⟨A, max B₀ A, hA, le_max_right _ _, hlower, ?_⟩
  intro z w
  exact le_trans (hupper z w)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end LyubarskiiNes.GeneralLattice
