import LeanCode.RationalDensity.RationalPositive.Basic

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- A positive lower bound on a real `tsum` forces genuine summability. This is
the product-indexed version of the real-`tsum` bookkeeping used in the final
assembly theorem. -/
theorem summable_of_pos_le_tsum {ι : Type*} {a : ℝ} {f : ι → ℝ}
    (ha : 0 < a) (hle : a ≤ ∑' i, f i) : Summable f := by
  by_contra hf
  rw [tsum_eq_zero_of_not_summable hf] at hle
  linarith

/-- The denominator index set is nonempty under the paper's gap hypothesis. -/
lemma q_pos_of_gap {p q : ℕ} (hgap : q ≥ p + 2) : 0 < q := by
  omega

/-- The numerator index set is nonempty under the positive-density hypotheses. -/
lemma p_pos_of_density {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (_hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    0 < p := by
  by_contra hp0
  have hp : p = 0 := Nat.eq_zero_of_not_pos hp0
  have hprod_pos : 0 < α * β := mul_pos hα hβ
  rw [hαβ, hp] at hprod_pos
  norm_num at hprod_pos

/-- Positivity of the rational-Zak scale `γ = α q`. -/
lemma rationalZakGamma_pos {α : ℝ} {q : ℕ}
    (hα : 0 < α) (hq : 0 < q) :
    0 < rationalZakGamma α q := by
  unfold rationalZakGamma
  positivity

/-- Positivity of the fiberization scale `η = γ / p` under the paper's
positive rational-density hypotheses. -/
lemma rationalZakEta_pos {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    0 < rationalZakEta α p q := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq : 0 < q := q_pos_of_gap hgap
  unfold rationalZakEta rationalZakGamma
  positivity

/-- The fiberization scale agrees with `β⁻¹` under `αβ = p/q`. -/
lemma rationalZakEta_eq_inv_beta {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    rationalZakEta α p q = β⁻¹ := by
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq_nat : 0 < q := q_pos_of_gap hgap
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hp_nat
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq_nat
  have hβne : β ≠ 0 := ne_of_gt hβ
  unfold rationalZakEta rationalZakGamma
  field_simp [hp, hq, hβne] at hαβ ⊢
  nlinarith

/-- The inverse base-frequency period is `p / γ`; this is the arithmetic
identity behind the partition of the frequency interval into `p` rational
subintervals. -/
lemma rationalZakEta_inv_eq_p_div_gamma {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    (rationalZakEta α p q)⁻¹ = (p : ℝ) / rationalZakGamma α q := by
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq_nat : 0 < q := q_pos_of_gap hgap
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hp_nat
  have hγ : rationalZakGamma α q ≠ 0 :=
    ne_of_gt (rationalZakGamma_pos hα hq_nat)
  unfold rationalZakEta
  field_simp [hp, hγ]

/-- Consecutive rational frequency endpoints are ordered when the frequency
period `γ` is positive. -/
lemma nat_div_gamma_le_succ_div_gamma {γ : ℝ} (hγ : 0 < γ) (k : ℕ) :
    (k : ℝ) / γ ≤ ((k + 1 : ℕ) : ℝ) / γ := by
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ k
  exact div_le_div_of_nonneg_right hk hγ.le

/-- Nonnegative rational frequency endpoint. -/
lemma zero_le_nat_div_gamma {γ : ℝ} (hγ : 0 < γ) (k : ℕ) :
    0 ≤ (k : ℝ) / γ := by
  positivity

/-- Translating the base frequency interval by `k / γ` gives the `k`th
subinterval in the partition of `(0, p / γ]`. -/
lemma frequency_shift_integral_Ioc
    {γ : ℝ} (hγ : 0 < γ) (F : ℝ → ℝ) (k : ℕ) :
    (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + (k : ℝ) / γ)) =
      ∫ ω in Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ), F ω := by
  have hinv_nonneg : 0 ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hstep : γ⁻¹ + (k : ℝ) / γ = ((k + 1 : ℕ) : ℝ) / γ := by
    calc
      γ⁻¹ + (k : ℝ) / γ = (1 : ℝ) / γ + (k : ℝ) / γ := by
        rw [one_div]
      _ = ((1 : ℝ) + (k : ℝ)) / γ := by
        rw [add_div]
      _ = ((k + 1 : ℕ) : ℝ) / γ := by
        norm_num [Nat.cast_add, add_comm]
  calc
    (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + (k : ℝ) / γ)) =
        ∫ ξ in (0 : ℝ)..γ⁻¹, F (ξ + (k : ℝ) / γ) := by
          rw [intervalIntegral.integral_of_le hinv_nonneg]
    _ = ∫ ω in (0 : ℝ) + (k : ℝ) / γ..γ⁻¹ + (k : ℝ) / γ, F ω := by
          rw [intervalIntegral.integral_comp_add_right]
    _ = ∫ ω in ((k : ℝ) / γ)..(((k + 1 : ℕ) : ℝ) / γ), F ω := by
          simp [hstep]
    _ = ∫ ω in Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ), F ω := by
          rw [intervalIntegral.integral_of_le
            (nat_div_gamma_le_succ_div_gamma hγ k)]

/-- Summing over adjacent rational frequency subintervals gives the integral
over the whole interval `(0, p / γ]`. -/
lemma frequency_partition_integral_range
    {γ : ℝ} (hγ : 0 < γ) (F : ℝ → ℝ) (p : ℕ)
    (hint : ∀ k < p,
      IntervalIntegrable F (volume : Measure ℝ)
        ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ)) :
    Finset.sum (Finset.range p) (fun k =>
        ∫ ω in Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ), F ω) =
      ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω := by
  let a : ℕ → ℝ := fun k => (k : ℝ) / γ
  have hsum :=
    intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (f := F) (μ := (volume : Measure ℝ)) (n := p)
      (by
        intro k hk
        simpa [a] using hint k hk)
  calc
    Finset.sum (Finset.range p) (fun k =>
        ∫ ω in Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ), F ω) =
        Finset.sum (Finset.range p) (fun k =>
          ∫ ω in ((k : ℝ) / γ)..(((k + 1 : ℕ) : ℝ) / γ), F ω) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [intervalIntegral.integral_of_le
            (nat_div_gamma_le_succ_div_gamma hγ k)]
    _ = ∫ ω in (0 : ℝ)..((p : ℝ) / γ), F ω := by
          simpa [a] using hsum
    _ = ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω := by
          rw [intervalIntegral.integral_of_le
            (zero_le_nat_div_gamma hγ p)]

/-- Range-indexed form of the frequency partition after translating every
subinterval back to the base interval. -/
lemma frequency_shift_partition_integral_range
    {γ : ℝ} (hγ : 0 < γ) (F : ℝ → ℝ) (p : ℕ)
    (hint : ∀ k < p,
      IntervalIntegrable F (volume : Measure ℝ)
        ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ)) :
    Finset.sum (Finset.range p) (fun k =>
        ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + (k : ℝ) / γ)) =
      ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω := by
  calc
    Finset.sum (Finset.range p) (fun k =>
        ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + (k : ℝ) / γ)) =
        Finset.sum (Finset.range p) (fun k =>
          ∫ ω in Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ), F ω) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [frequency_shift_integral_Ioc hγ F k]
    _ = ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω :=
          frequency_partition_integral_range hγ F p hint

/-- `Fin p`-indexed form of the frequency partition, matching the matrix-row
indexing used in the rational Zak fibers. -/
lemma frequency_shift_partition_integral_fin
    {γ : ℝ} (hγ : 0 < γ) (F : ℝ → ℝ) (p : ℕ)
    (hint : ∀ k < p,
      IntervalIntegrable F (volume : Measure ℝ)
        ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ)) :
    (∑ r : Fin p,
        ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + ((r : ℕ) : ℝ) / γ)) =
      ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω := by
  let G : ℕ → ℝ := fun k =>
    ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + (k : ℝ) / γ)
  calc
    (∑ r : Fin p,
        ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹, F (ξ + ((r : ℕ) : ℝ) / γ)) =
        Finset.sum (Finset.range p) G := by
          simpa [G] using (Fin.sum_univ_eq_sum_range G p)
    _ = ∫ ω in Set.Ioc (0 : ℝ) ((p : ℝ) / γ), F ω := by
          simpa [G] using frequency_shift_partition_integral_range hγ F p hint

/-- Frequency-periodicity of the concrete paper-side rational Zak matrix. -/
lemma rationalZakPMatrixH1_freq_period {α : ℝ} {p q : ℕ}
    (hγ : rationalZakGamma α q ≠ 0) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    rationalZakPMatrixH1 α p q (z.1, z.2 + (rationalZakGamma α q)⁻¹) s t =
      rationalZakPMatrixH1 α p q z s t := by
  unfold rationalZakPMatrixH1
  exact Zak.zakTransform_freq_period (ρ := rationalZakGamma α q) hγ gaussianH1C
    (z.1 + α * ↑↑t + rationalZakGamma α q * ↑↑s / ↑p) z.2

/-- Spatial quasi-periodicity of the concrete paper-side rational Zak matrix. -/
lemma rationalZakPMatrixH1_add_gamma (α : ℝ) (p q : ℕ)
    (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    rationalZakPMatrixH1 α p q (z.1 + rationalZakGamma α q, z.2) s t =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (rationalZakGamma α q : ℂ) *
        (z.2 : ℂ)) * rationalZakPMatrixH1 α p q z s t := by
  unfold rationalZakPMatrixH1
  let γ : ℝ := rationalZakGamma α q
  let y : ℝ := z.1 + α * ((t : ℕ) : ℝ) + γ * ((s : ℕ) : ℝ) / (p : ℝ)
  have hy :
      (z.1 + γ) + α * ((t : ℕ) : ℝ) + γ * ((s : ℕ) : ℝ) / (p : ℝ) =
        y + γ := by
    dsimp [y]
    ring
  have h := Zak.zakTransform_add_period γ gaussianH1C y z.2
  calc
    Zak.zakTransform γ gaussianH1C
        ((z.1 + γ) + α * ((t : ℕ) : ℝ) +
          γ * ((s : ℕ) : ℝ) / (p : ℝ)) z.2 =
        Zak.zakTransform γ gaussianH1C (y + γ) z.2 := by
      rw [hy]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ)) *
          Zak.zakTransform γ gaussianH1C y z.2 := h
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ)) *
          Zak.zakTransform γ gaussianH1C
            (z.1 + α * ((t : ℕ) : ℝ) +
              γ * ((s : ℕ) : ℝ) / (p : ℝ)) z.2 := by
      rfl

/-- Norm-periodicity of the concrete paper-side rational Zak matrix in the
frequency coordinate. -/
lemma rationalZakPMatrixH1_norm_freq_period {α : ℝ} {p q : ℕ}
    (hγ : rationalZakGamma α q ≠ 0) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    ‖rationalZakPMatrixH1 α p q (z.1, z.2 + (rationalZakGamma α q)⁻¹) s t‖ =
      ‖rationalZakPMatrixH1 α p q z s t‖ := by
  rw [rationalZakPMatrixH1_freq_period hγ z s t]

/-- Norm-periodicity of the concrete paper-side rational Zak matrix in the
spatial coordinate. -/
lemma rationalZakPMatrixH1_norm_add_gamma (α : ℝ) (p q : ℕ)
    (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    ‖rationalZakPMatrixH1 α p q (z.1 + rationalZakGamma α q, z.2) s t‖ =
      ‖rationalZakPMatrixH1 α p q z s t‖ := by
  unfold rationalZakPMatrixH1
  let γ : ℝ := rationalZakGamma α q
  let y : ℝ := z.1 + α * ((t : ℕ) : ℝ) + γ * ((s : ℕ) : ℝ) / (p : ℝ)
  have hy :
      (z.1 + γ) + α * ((t : ℕ) : ℝ) + γ * ((s : ℕ) : ℝ) / (p : ℝ) =
        y + γ := by
    dsimp [y]
    ring
  have h := Zak.zakTransform_add_period γ gaussianH1C y z.2
  have hnorm_exp :
      ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ))‖ =
        1 := by
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ) =
          ((2 * Real.pi * γ * z.2 : ℝ) : ℂ) * Complex.I := by
      norm_num [Complex.ofReal_mul]
      ring
    rw [harg]
    exact Complex.norm_exp_ofReal_mul_I _
  calc
    ‖Zak.zakTransform γ gaussianH1C
        ((z.1 + γ) + α * ((t : ℕ) : ℝ) +
          γ * ((s : ℕ) : ℝ) / (p : ℝ)) z.2‖ =
        ‖Zak.zakTransform γ gaussianH1C (y + γ) z.2‖ := by
      rw [hy]
    _ = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ)) *
          Zak.zakTransform γ gaussianH1C y z.2‖ := by
      rw [h]
    _ = ‖Zak.zakTransform γ gaussianH1C y z.2‖ := by
      rw [norm_mul, hnorm_exp, one_mul]
    _ = ‖Zak.zakTransform γ gaussianH1C
        (z.1 + α * ((t : ℕ) : ℝ) + γ * ((s : ℕ) : ℝ) / (p : ℝ)) z.2‖ := by
      rfl

/-- A continuous function with separately periodic norm on positive periods is
bounded globally by its bound on one compact fundamental rectangle. -/
lemma exists_norm_bound_of_continuous_norm_periodic_prod
    {E : Type*} [SeminormedAddGroup E]
    {f : ℝ × ℝ → E} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hf : Continuous f)
    (hper₁ : ∀ z : ℝ × ℝ, ‖f (z.1 + a, z.2)‖ = ‖f z‖)
    (hper₂ : ∀ z : ℝ × ℝ, ‖f (z.1, z.2 + b)‖ = ‖f z‖) :
    ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖f z‖ ≤ C := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  rcases hK.exists_bound_of_continuousOn hf.continuousOn with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro z
  have hpx : Function.Periodic (fun x : ℝ => ‖f (x, z.2)‖) a := by
    intro x
    simpa using hper₁ (x, z.2)
  rcases hpx.exists_mem_Ico ha z.1 0 with ⟨x0, hx0, hx0eq⟩
  have hpy : Function.Periodic (fun y : ℝ => ‖f (x0, y)‖) b := by
    intro y
    simpa using hper₂ (x0, y)
  rcases hpy.exists_mem_Ico hb z.2 0 with ⟨y0, hy0, hy0eq⟩
  have hx0Icc : x0 ∈ Set.Icc (0 : ℝ) a := ⟨hx0.1, by simpa using le_of_lt hx0.2⟩
  have hy0Icc : y0 ∈ Set.Icc (0 : ℝ) b := ⟨hy0.1, by simpa using le_of_lt hy0.2⟩
  calc
    ‖f z‖ = ‖f (x0, z.2)‖ := hx0eq
    _ = ‖f (x0, y0)‖ := hy0eq
    _ ≤ C := hC (x0, y0) ⟨hx0Icc, hy0Icc⟩

/-- Continuity of the concrete paper-side rational Zak matrix implies
entrywise boundedness, using its two norm-periodicities. -/
lemma rationalZakPMatrixH1_entries_bounded_of_continuous
    {α : ℝ} {p q : ℕ}
    (hγ : 0 < rationalZakGamma α q)
    (hP_cont : Continuous (rationalZakPMatrixH1 α p q)) :
    ∀ i j, ∃ Cij : ℝ, ∀ z, ‖rationalZakPMatrixH1 α p q z i j‖ ≤ Cij := by
  intro i j
  have hentry_cont : Continuous (fun z : ℝ × ℝ => rationalZakPMatrixH1 α p q z i j) := by
    exact (continuous_apply j).comp ((continuous_apply i).comp hP_cont)
  exact exists_norm_bound_of_continuous_norm_periodic_prod
    (f := fun z : ℝ × ℝ => rationalZakPMatrixH1 α p q z i j)
    hγ (inv_pos.mpr hγ) hentry_cont
    (rationalZakPMatrixH1_norm_add_gamma α p q · i j)
    (rationalZakPMatrixH1_norm_freq_period (ne_of_gt hγ) · i j)

/-- Frequency-periodicity of the adjoint-oriented rational Zak matrix, in the
operator norm shape used by the lower-bound compactness argument. -/
lemma rationalZakMatrix_mulVec_norm_freq_period {α : ℝ} {p q : ℕ}
    (hγ : rationalZakGamma α q ≠ 0) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖rationalZakMatrix α p q (z.1, z.2 + (rationalZakGamma α q)⁻¹) *ᵥ w‖ =
      ‖rationalZakMatrix α p q z *ᵥ w‖ := by
  have hP :
      rationalZakPMatrixH1 α p q (z.1, z.2 + (rationalZakGamma α q)⁻¹) =
        rationalZakPMatrixH1 α p q z := by
    ext s t
    exact rationalZakPMatrixH1_freq_period hγ z s t
  unfold rationalZakMatrix
  rw [hP]

/-- Spatial norm-periodicity of the adjoint-oriented rational Zak matrix, in
the operator norm shape used by the lower-bound compactness argument. -/
lemma rationalZakMatrix_mulVec_norm_add_gamma (α : ℝ) (p q : ℕ)
    (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖rationalZakMatrix α p q (z.1 + rationalZakGamma α q, z.2) *ᵥ w‖ =
      ‖rationalZakMatrix α p q z *ᵥ w‖ := by
  let γ : ℝ := rationalZakGamma α q
  let c : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ))
  have hc_norm : ‖star c‖ = 1 := by
    have hc : ‖c‖ = 1 := by
      dsimp [c]
      have harg :
          2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (z.2 : ℂ) =
            ((2 * Real.pi * γ * z.2 : ℝ) : ℂ) * Complex.I := by
        norm_num [Complex.ofReal_mul]
        ring
      rw [harg]
      exact Complex.norm_exp_ofReal_mul_I _
    simpa using hc
  have hvec :
      rationalZakMatrix α p q (z.1 + rationalZakGamma α q, z.2) *ᵥ w =
        (star c) • (rationalZakMatrix α p q z *ᵥ w) := by
    ext i
    dsimp [γ, c]
    simp [Matrix.mulVec, dotProduct, rationalZakMatrix,
      rationalZakPMatrixH1_add_gamma, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [hvec, norm_smul, hc_norm, one_mul]

/-- The unit sphere in a positive-dimensional finite complex vector space is
nonempty. -/
lemma fin_complex_unit_sphere_nonempty {p : ℕ} (hp : 0 < p) :
    (Metric.sphere (0 : Fin p → ℂ) 1).Nonempty := by
  classical
  let i : Fin p := ⟨0, hp⟩
  let e : Fin p → ℂ := Pi.single i (1 : ℂ)
  refine ⟨e, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  rw [Pi.norm_def]
  rw [← NNReal.coe_one]
  rw [NNReal.coe_inj]
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [e]
    · simp [e, Pi.single_eq_of_ne hji]
  · have hi : ‖e i‖₊ = 1 := by
      simp [e]
    calc
      1 = ‖e i‖₊ := hi.symm
      _ ≤ Finset.univ.sup (fun b => ‖e b‖₊) :=
        Finset.le_sup (s := Finset.univ) (f := fun b => ‖e b‖₊) (Finset.mem_univ i)

/-- A continuous matrix field with positive periods and pointwise injective
fibers has a single homogeneous lower bound, provided the matrix-vector norm is
periodic in both coordinates. -/
lemma exists_uniform_lower_bound_of_continuous_periodic_injective
    {m n : Type*} [Fintype m] [Fintype n]
    (M : ℝ × ℝ → Matrix m n ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hM : Continuous M)
    (hper₁ : ∀ z w, ‖M (z.1 + a, z.2) *ᵥ w‖ = ‖M z *ᵥ w‖)
    (hper₂ : ∀ z w, ‖M (z.1, z.2 + b) *ᵥ w‖ = ‖M z *ᵥ w‖)
    (hinj : ∀ z, Function.Injective (M z).mulVec)
    (hsphere : (Metric.sphere (0 : n → ℂ) 1).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ z w, A * ‖w‖ ^ 2 ≤ ‖M z *ᵥ w‖ ^ 2 := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) b
  let S : Set ((ℝ × ℝ) × (n → ℂ)) := K ×ˢ Metric.sphere (0 : n → ℂ) 1
  let q : ((ℝ × ℝ) × (n → ℂ)) → ℝ := fun zw => ‖M zw.1 *ᵥ zw.2‖ ^ 2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hSphereCompact : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere _ _
  have hScompact : IsCompact S := hK.prod hSphereCompact
  have hKnonempty : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    constructor <;> constructor <;> linarith
  have hSnonempty : S.Nonempty := hKnonempty.prod hsphere
  have hqcont : Continuous q := by
    unfold q
    fun_prop
  obtain ⟨zw0, hzw0S, hzw0_min⟩ := hScompact.exists_isMinOn
    hSnonempty hqcont.continuousOn
  refine ⟨q zw0, ?_, ?_⟩
  · have hw_sphere : zw0.2 ∈ Metric.sphere (0 : n → ℂ) 1 := hzw0S.2
    have hw_ne : zw0.2 ≠ 0 := by
      intro hw0
      have hdist : dist zw0.2 (0 : n → ℂ) = 1 := by
        simpa [Metric.mem_sphere] using hw_sphere
      simp [hw0] at hdist
    have hMw_ne : M zw0.1 *ᵥ zw0.2 ≠ 0 := by
      intro hzero
      have hker : (M zw0.1).mulVec zw0.2 = (M zw0.1).mulVec 0 := by
        simpa using hzero
      exact hw_ne ((hinj zw0.1) hker)
    have hnorm_pos : 0 < ‖M zw0.1 *ᵥ zw0.2‖ := norm_pos_iff.mpr hMw_ne
    have hsq_pos : 0 < ‖M zw0.1 *ᵥ zw0.2‖ ^ 2 := sq_pos_of_pos hnorm_pos
    simpa [q] using hsq_pos
  · have hunit : ∀ z w, w ∈ Metric.sphere (0 : n → ℂ) 1 →
        q zw0 ≤ ‖M z *ᵥ w‖ ^ 2 := by
      intro z w hw
      have hpx : Function.Periodic (fun x : ℝ => ‖M (x, z.2) *ᵥ w‖ ^ 2) a := by
        intro x
        exact congrArg (fun r : ℝ => r ^ 2) (hper₁ (x, z.2) w)
      rcases hpx.exists_mem_Ico ha z.1 0 with ⟨x0, hx0, hx0eq⟩
      have hpy : Function.Periodic (fun y : ℝ => ‖M (x0, y) *ᵥ w‖ ^ 2) b := by
        intro y
        exact congrArg (fun r : ℝ => r ^ 2) (hper₂ (x0, y) w)
      rcases hpy.exists_mem_Ico hb z.2 0 with ⟨y0, hy0, hy0eq⟩
      have hx0Icc : x0 ∈ Set.Icc (0 : ℝ) a := ⟨hx0.1, by simpa using le_of_lt hx0.2⟩
      have hy0Icc : y0 ∈ Set.Icc (0 : ℝ) b := ⟨hy0.1, by simpa using le_of_lt hy0.2⟩
      have hxy : ‖M z *ᵥ w‖ ^ 2 = ‖M (x0, y0) *ᵥ w‖ ^ 2 := by
        calc
          ‖M z *ᵥ w‖ ^ 2 = ‖M (x0, z.2) *ᵥ w‖ ^ 2 := hx0eq
          _ = ‖M (x0, y0) *ᵥ w‖ ^ 2 := hy0eq
      have hmem : ((x0, y0), w) ∈ S := ⟨⟨hx0Icc, hy0Icc⟩, hw⟩
      exact le_trans (hzw0_min hmem) (by simp [q, hxy])
    intro z w
    exact (Zak.mulVec_norm_sq_lower_bound_of_unit_sphere (M z) (hunit z)) w

/-- Pointwise injectivity of the concrete rational Zak matrix globalizes to a
single lower matrix bound by continuity and rational-Zak periodicity. -/
lemma rationalZakMatrix_uniform_lower_bound_of_injective {α : ℝ} {p q : ℕ}
    (hγ : 0 < rationalZakGamma α q)
    (hM_cont : Continuous (rationalZakMatrix α p q))
    (hinj : ∀ z, Function.Injective (rationalZakMatrix α p q z).mulVec)
    (hsphere : (Metric.sphere (0 : Fin p → ℂ) 1).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ z w,
      A * ‖w‖ ^ 2 ≤ ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2 :=
  exists_uniform_lower_bound_of_continuous_periodic_injective
    (M := rationalZakMatrix α p q) hγ (inv_pos.mpr hγ) hM_cont
    (rationalZakMatrix_mulVec_norm_add_gamma α p q)
    (rationalZakMatrix_mulVec_norm_freq_period (ne_of_gt hγ))
    hinj hsphere

/-- A nonzero cyclic consecutive minor of the concrete rational-Zak matrix
implies pointwise injectivity of its `mulVec` map. -/
lemma rationalZakMatrix_injective_of_cyclic_minor
    {α : ℝ} {p q : ℕ} [NeZero q] (z : ℝ × ℝ)
    (hdet : ∃ j : Fin q,
      ((rationalZakMatrix α p q z).submatrix
        (LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j) id).det ≠ 0) :
    Function.Injective (rationalZakMatrix α p q z).mulVec := by
  classical
  rcases hdet with ⟨j, hdetj⟩
  have hrank : (rationalZakMatrix α p q z).rank = p := by
    exact LyubarskiiNes.FrobeniusDeterminant.rank_eq_of_fin_cyclic_consecutive_minor_ne_zero
      (rationalZakMatrix α p q z) j hdetj
  exact (Zak.mulVec_injective_iff_rank_eq_card_width (rationalZakMatrix α p q z)).2
    (by simpa using hrank)

/-- Nonzero cyclic consecutive minors at every point give pointwise injectivity
of the concrete rational-Zak matrix field. -/
lemma rationalZakMatrix_injective_of_cyclic_minor_field
    {α : ℝ} {p q : ℕ} [NeZero q]
    (hminor : ∀ z : ℝ × ℝ, ∃ j : Fin q,
      ((rationalZakMatrix α p q z).submatrix
        (LyubarskiiNes.FrobeniusDeterminant.cyclicConsecutiveRows p q j) id).det ≠ 0) :
    ∀ z, Function.Injective (rationalZakMatrix α p q z).mulVec := by
  intro z
  exact rationalZakMatrix_injective_of_cyclic_minor z (hminor z)

/-- The scalar first-Hermite Gaussian-Zak closed-form formula implies the
entrywise closed-form identity for the concrete rational-Zak matrix. -/
lemma rationalZakPMatrixH1_closedForm_of_gaussianZakH1
    {α : ℝ} {p q : ℕ}
    (hformula : ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH1C x ω = gaussianZakH1ClosedForm γ ω x)
    (hγ : 0 < rationalZakGamma α q) :
    ∀ z s t,
      rationalZakPMatrixH1 α p q z s t =
        gaussianZakH1ClosedForm (rationalZakGamma α q) z.2
          (z.1 + α * ((t : ℕ) : ℝ) +
            rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) := by
  intro z s t
  unfold rationalZakPMatrixH1
  exact hformula (rationalZakGamma α q) hγ
    (z.1 + α * ((t : ℕ) : ℝ) +
      rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) z.2

/-- At the rational Zak sample points, the Gaussian-Zak theta argument splits
into the primitive theta matrix base point plus the `t/q` and `s/p` shifts. -/
lemma gaussianZakThetaArg_rational_sample
    {α : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    gaussianZakThetaArg (rationalZakGamma α q) z.2
      (z.1 + α * ((t : ℕ) : ℝ) +
        rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) =
      ((rationalZakGamma α q : ℂ)⁻¹ * (z.1 : ℂ) +
          Complex.I * (z.2 : ℂ) / (rationalZakGamma α q : ℂ)) +
        ((t : ℕ) : ℂ) / (q : ℂ) + ((s : ℕ) : ℂ) / (p : ℂ) := by
  unfold gaussianZakThetaArg rationalZakGamma
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp [hαc, hqc]
  ring

/-- The theta differential factor in the closed first-Hermite Zak formula is
the corresponding primitive theta-derivative matrix entry at rational samples. -/
lemma gaussianZakDTheta_rational_sample_eq_primitive
    {α : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (z : ℝ × ℝ) (s : Fin p) (t : Fin q) :
    gaussianZakDTheta (rationalZakGamma α q) z.2
      (z.1 + α * ((t : ℕ) : ℝ) +
        rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) =
      LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix p q
        (gaussianZakTau (rationalZakGamma α q))
        ((rationalZakGamma α q : ℂ) * (z.2 : ℂ))
        ((rationalZakGamma α q : ℂ)⁻¹ * (z.1 : ℂ) +
          Complex.I * (z.2 : ℂ) / (rationalZakGamma α q : ℂ)) t s := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  have harg := gaussianZakThetaArg_rational_sample (p := p) (q := q) hα z s t
  unfold gaussianZakDTheta LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix
  rw [LyubarskiiNes.FrobeniusDeterminant.scaledDeriv_thetaShift]
  · rw [harg]
    unfold gaussianZakTau LyubarskiiNes.TorsionJets.paperDerivScale
      LyubarskiiNes.ThetaFunctions.thetaShift LyubarskiiNes.ThetaFunctions.theta
    ring
  · simpa [gaussianZakTau] using gaussianZakTau_im_pos hγ

/-- The paper-side rational Zak matrix entry is a nonzero global prefactor and
phase factor times the primitive theta-derivative matrix entry. -/
lemma rationalZakPMatrixH1_eq_scaled_primitive
    {α : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (z : ℝ × ℝ) (s : Fin p) (t : Fin q)
    (hformula : ∀ γ : ℝ, 0 < γ → ∀ x ω : ℝ,
      Zak.zakTransform γ gaussianH1C x ω = gaussianZakH1ClosedForm γ ω x) :
    rationalZakPMatrixH1 α p q z s t =
      (-Complex.I / (rationalZakGamma α q : ℂ) ^ 2 *
        Complex.exp (-(Real.pi : ℂ) * (z.2 : ℂ) ^ 2)) *
      gaussianZakPhase z.2
        (z.1 + α * ((t : ℕ) : ℝ) +
          rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) *
      LyubarskiiNes.FrobeniusDeterminant.primitiveThetaDerivativeMatrix p q
        (gaussianZakTau (rationalZakGamma α q))
        ((rationalZakGamma α q : ℂ) * (z.2 : ℂ))
        ((rationalZakGamma α q : ℂ)⁻¹ * (z.1 : ℂ) +
          Complex.I * (z.2 : ℂ) / (rationalZakGamma α q : ℂ)) t s := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  rw [rationalZakPMatrixH1_closedForm_of_gaussianZakH1 hformula hγ]
  unfold gaussianZakH1ClosedForm
  rw [gaussianZakDTheta_rational_sample_eq_primitive (p := p) (q := q) hα z s t]

/-- The Gaussian-Zak phase is multiplicative over addition of real arguments. -/
lemma gaussianZakPhase_add (ω a b : ℝ) :
    gaussianZakPhase ω (a + b) =
      gaussianZakPhase ω a * gaussianZakPhase ω b := by
  unfold gaussianZakPhase gaussianZakPhaseSlope
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_add]
  ring

/-- The Gaussian-Zak closed-form identity implies continuity of the concrete
paper-side rational Zak matrix. -/
lemma continuous_rationalZakPMatrixH1_of_closedForm {α : ℝ} {p q : ℕ}
    (hγ : 0 < rationalZakGamma α q)
    (hclosed : ∀ z s t,
      rationalZakPMatrixH1 α p q z s t =
        gaussianZakH1ClosedForm (rationalZakGamma α q) z.2
          (z.1 + α * ((t : ℕ) : ℝ) +
            rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ))) :
    Continuous (rationalZakPMatrixH1 α p q) := by
  apply continuous_matrix
  intro s t
  have hcf : Continuous fun z : ℝ × ℝ =>
      gaussianZakH1ClosedForm (rationalZakGamma α q) z.2
        (z.1 + α * ((t : ℕ) : ℝ) +
          rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) := by
    have hbase := continuous_gaussianZakH1ClosedForm (rationalZakGamma α q) hγ
    have hmap : Continuous fun z : ℝ × ℝ =>
        (z.1 + α * ((t : ℕ) : ℝ) +
          rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ), z.2) := by
      continuity
    exact hbase.comp hmap
  have hfun :
      (fun z : ℝ × ℝ => rationalZakPMatrixH1 α p q z s t) =
        fun z : ℝ × ℝ =>
          gaussianZakH1ClosedForm (rationalZakGamma α q) z.2
            (z.1 + α * ((t : ℕ) : ℝ) +
              rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) := by
    funext z
    exact hclosed z s t
  rw [hfun]
  exact hcf

/-- Continuity of a paper-side matrix field transfers to its adjoint-oriented
residual-shape field. -/
lemma continuous_conjTranspose_matrix_field
    {p q : ℕ} {P : ℝ × ℝ → Matrix (Fin p) (Fin q) ℂ}
    (hP : Continuous P) :
    Continuous (fun z => (P z)ᴴ) := by
  apply continuous_matrix
  intro i j
  change Continuous fun z => star (P z j i)
  exact Continuous.star ((continuous_apply i).comp ((continuous_apply j).comp hP))

/-- Separate boundedness of the paper-side matrix entries transfers to the
adjoint-oriented residual-shape matrix entries. -/
lemma conjTranspose_matrix_field_entries_bounded
    {p q : ℕ} {P : ℝ × ℝ → Matrix (Fin p) (Fin q) ℂ}
    (hP : ∀ i j, ∃ Cij : ℝ, ∀ z, ‖P z i j‖ ≤ Cij) :
    ∀ i j, ∃ Cij : ℝ, ∀ z, ‖(P z)ᴴ i j‖ ≤ Cij := by
  intro i j
  rcases hP j i with ⟨Cij, hCij⟩
  refine ⟨Cij, ?_⟩
  intro z
  simpa using hCij z

/-- A uniform bound on the entries of the concrete rational-Zak matrix field is
enough to supply the global upper matrix inequality in the final residual. -/
lemma rationalZakMatrix_uniform_upper_bound_of_entry_bound
    {p q : ℕ}
    (M : ℝ × ℝ → Matrix (Fin q) (Fin p) ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z i j, ‖M z i j‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z w,
      ‖M z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2 := by
  exact Zak.uniform_mulVec_norm_sq_upper_bound_of_entry_bound M hC hbound
end LyubarskiiNes.RationalDensity
