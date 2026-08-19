import LeanCode.RationalDensity.RationalPositive.BaseFiberLimit

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- Tsum form of `rationalPositive_spatial_sample_sq_integral_hasSum`. -/
theorem rationalPositive_spatial_sample_sq_integral_tsum
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑' k : ℤ,
      ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ‖(fun t : ℝ => x t)
          (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) =
      ∫ t : ℝ, ‖(fun u : ℝ => x u) t‖ ^ 2 :=
  (rationalPositive_spatial_sample_sq_integral_hasSum
    hα hβ hgap hαβ x).tsum_eq

/-- Tonelli/interchange for the nonnegative spatial sample-square series over
one rational-Zak spatial period. This is the missing bridge between the
fixed-fiber Parseval theorem, which produces a `tsum` at each spatial point, and
the global spatial periodization theorem, which sums the sample integrals. -/
theorem rationalPositive_spatial_sample_sq_integral_tsum_inside
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∑' k : ℤ,
          ‖(fun t : ℝ => x t)
            (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) =
      ∑' k : ℤ,
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ‖(fun t : ℝ => x t)
            (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  let η : ℝ := rationalZakEta α p q
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) η)
  let F : ℤ → ℝ → ℝ := fun k s =>
    ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  have hΦ :
      Integrable
        (fun t : ℝ => ‖(fun u : ℝ => x u) t‖ ^ 2)
        (volume : Measure ℝ) :=
    Zak.integrable_norm_sq_of_memLp_two (Lp.memLp x)
  have hF_int : ∀ k : ℤ, Integrable (F k) μ := by
    intro k
    dsimp [F, μ]
    have hglobal :
        Integrable
          (fun s : ℝ => ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2)
          (volume : Measure ℝ) := by
      simpa [sub_eq_add_neg] using hΦ.comp_add_right (-η * (k : ℝ))
    exact hglobal.mono_measure Measure.restrict_le_self
  have hsum_integral_norm :
      Summable fun k : ℤ => ∫ s, ‖F k s‖ ∂μ := by
    have hhas :=
      rationalPositive_spatial_sample_sq_integral_hasSum
        hα hβ hgap hαβ x
    have hfun :
        (fun k : ℤ => ∫ s, ‖F k s‖ ∂μ) =
          fun k : ℤ =>
            ∫ s in Set.Ioc (0 : ℝ) η,
              ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2 := by
      funext k
      simp [F, μ, Real.norm_of_nonneg (sq_nonneg _)]
    rw [hfun]
    simpa [η] using hhas.summable
  have hswap :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := F) hF_int hsum_integral_norm
  simpa [F, μ, η] using hswap.symm

/-- The `L²` norm of an ambient class is the integral of the squared norm of
its representative. -/
theorem rationalPositive_l2_norm_sq_eq_integral_norm_sq
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖x‖ ^ 2 = ∫ t : ℝ, ‖(fun u : ℝ => x u) t‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = RCLike.re (inner ℂ x x) := by
      exact InnerProductSpace.norm_sq_eq_re_inner x
    _ = RCLike.re (∫ t : ℝ, inner ℂ (x t) (x t)) := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ t : ℝ, RCLike.re (inner ℂ (x t) (x t)) := by
      exact (integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) x x)).symm
    _ = ∫ t : ℝ, ‖(fun u : ℝ => x u) t‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        change RCLike.re (inner ℂ (x t) (x t)) = ‖x t‖ ^ 2
        rw [inner_self_eq_norm_sq_to_K]
        change (((↑(‖x t‖) : ℂ) ^ 2).re) = ‖x t‖ ^ 2
        rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Honest scaled form of the iterated base-frequency Parseval identity. The
factor `η⁻¹` comes from the fixed-fiber Parseval theorem
`η * ∫ |fiber|² = ∑ |sample|²`; downstream frame constants must absorb this
positive scale. -/
theorem rationalPositiveBase_component_energy_iterated_identity_scaled
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x, (∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2) =
      (rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2 := by
  intro x
  let η : ℝ := rationalZakEta α p q
  let innerEnergy : ℝ → ℝ := fun s =>
    ∫ ω in Set.Ioc (0 : ℝ) η⁻¹,
      ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2
  let sampleEnergy : ℝ → ℝ := fun s =>
    ∑' k : ℤ,
      ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2
  have hae :=
    rationalPositiveBaseFrequencyFiber_integral_eq_inv_eta_tsum_ae
      hα hβ hgap hαβ x
  have hcongr :
      (∫ s in Set.Ioc (0 : ℝ) η, innerEnergy s) =
        ∫ s in Set.Ioc (0 : ℝ) η, η⁻¹ * sampleEnergy s := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [hae] with s hs hs_mem
    simpa [innerEnergy, sampleEnergy, η] using hs hs_mem
  calc
    (∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) η, innerEnergy s := by
          simp [innerEnergy, η]
    _ = ∫ s in Set.Ioc (0 : ℝ) η, η⁻¹ * sampleEnergy s := hcongr
    _ = η⁻¹ * (∫ s in Set.Ioc (0 : ℝ) η, sampleEnergy s) := by
          rw [MeasureTheory.integral_const_mul]
    _ = η⁻¹ * (∑' k : ℤ,
        ∫ s in Set.Ioc (0 : ℝ) η,
          ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2) := by
          rw [rationalPositive_spatial_sample_sq_integral_tsum_inside
            hα hβ hgap hαβ x]
    _ = η⁻¹ * (∫ t : ℝ, ‖(fun u : ℝ => x u) t‖ ^ 2) := by
          rw [rationalPositive_spatial_sample_sq_integral_tsum
            hα hβ hgap hαβ x]
    _ = (rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2 := by
          rw [← rationalPositive_l2_norm_sq_eq_integral_norm_sq x]

/-- For each fixed spatial point, the `p` shifted base-frequency fiber energies
over the short frequency interval partition the whole `η⁻¹` frequency interval.

The remaining hypothesis is only the interval-integrability bookkeeping needed
by `intervalIntegral.sum_integral_adjacent_intervals`; the arithmetic and
adjacent-interval partition are discharged here. -/
lemma rationalPositive_frequency_partition_integral
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ)
    (hint : ∀ k < p,
      IntervalIntegrable
        (fun ω : ℝ =>
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2)
        (volume : Measure ℝ)
        ((k : ℝ) / rationalZakGamma α q)
        (((k + 1 : ℕ) : ℝ) / rationalZakGamma α q)) :
    (∑ r : Fin p,
        ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2) =
      ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  let F : ℝ → ℝ := fun ω =>
    ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2
  have hpart :=
    frequency_shift_partition_integral_fin
      (γ := rationalZakGamma α q) hγ F p hint
  simpa [F, rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ] using hpart

/-- The square norm of a fixed base-frequency fiber is interval-integrable on
each rational subinterval appearing in the frequency partition. -/
lemma rationalPositiveBaseFrequencyFiber_intervalIntegrable_sq
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) :
    ∀ k < p,
      IntervalIntegrable
        (fun ω : ℝ =>
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2)
        (volume : Measure ℝ)
        ((k : ℝ) / rationalZakGamma α q)
        (((k + 1 : ℕ) : ℝ) / rationalZakGamma α q) := by
  intro k hk
  let F : ℝ → ℝ := fun ω =>
    ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2
  let γ : ℝ := rationalZakGamma α q
  have hγ : 0 < γ := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  have hmem :=
    rationalPositiveBaseFrequencyFiber_memLp hα hβ hgap hαβ x s
  have hsq :
      Integrable F ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm
      hmem.aestronglyMeasurable] at hmem
    simpa [F] using hmem
  have hsq_on :
      IntegrableOn F
        (Set.Ioc (0 : ℝ) ((p : ℝ) / γ)) (volume : Measure ℝ) := by
    simpa [IntegrableOn, F, γ,
      rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ] using hsq
  have hupper :
      (((k + 1 : ℕ) : ℝ) / γ) ≤ (p : ℝ) / γ := by
    have hk_succ : k + 1 ≤ p := Nat.succ_le_of_lt hk
    have hk_real : (((k + 1 : ℕ) : ℝ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hk_succ
    exact div_le_div_of_nonneg_right hk_real hγ.le
  have hsub :
      Set.Ioc ((k : ℝ) / γ) (((k + 1 : ℕ) : ℝ) / γ) ⊆
        Set.Ioc (0 : ℝ) ((p : ℝ) / γ) := by
    intro ω hω
    exact ⟨lt_of_le_of_lt (zero_le_nat_div_gamma hγ k) hω.1,
      le_trans hω.2 hupper⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (nat_div_gamma_le_succ_div_gamma hγ k)]
  exact hsq_on.mono_set hsub

/-- Hypothesis-free form of the fixed-spatial frequency partition for the
concrete base-frequency fiber. -/
lemma rationalPositive_frequency_partition_integral_of_memLp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) :
    (∑ r : Fin p,
        ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2) =
      ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 :=
  rationalPositive_frequency_partition_integral hα hβ hgap hαβ x s
    (rationalPositiveBaseFrequencyFiber_intervalIntegrable_sq
      hα hβ hgap hαβ x s)

/-- Fixed-spatial frequency partition with the finite component sum inside the
short-interval integral. This is the form that appears after applying Fubini to
the fundamental rectangle. -/
lemma rationalPositive_frequency_partition_integral_sum_inside
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) :
    (∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
        (∑ r : Fin p,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2)) =
      ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
  let γ : ℝ := rationalZakGamma α q
  let F : ℝ → ℝ := fun ω =>
    ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2
  have hγ : 0 < γ := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  have hγ_inv_nonneg : 0 ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hshift : ∀ r : Fin p,
      IntervalIntegrable
        (fun ξ : ℝ => F (ξ + ((r : ℕ) : ℝ) / γ))
        (volume : Measure ℝ) (0 : ℝ) γ⁻¹ := by
    intro r
    have hbase :=
      rationalPositiveBaseFrequencyFiber_intervalIntegrable_sq
        hα hβ hgap hαβ x s (r : ℕ) r.isLt
    have hcomp := hbase.comp_add_right (((r : ℕ) : ℝ) / γ)
    have hleft : ((r : ℕ) : ℝ) / γ - ((r : ℕ) : ℝ) / γ = (0 : ℝ) := by
      ring
    have hright :
        ((((r : ℕ) : ℝ) + 1) / γ - ((r : ℕ) : ℝ) / γ) = γ⁻¹ := by
      field_simp [ne_of_gt hγ]
      norm_num
    simpa [F, γ, hleft, hright] using hcomp
  have hsum_interval :
      (∫ ξ in (0 : ℝ)..γ⁻¹,
          (∑ r : Fin p, F (ξ + ((r : ℕ) : ℝ) / γ))) =
        ∑ r : Fin p, ∫ ξ in (0 : ℝ)..γ⁻¹,
          F (ξ + ((r : ℕ) : ℝ) / γ) := by
    simpa only [Finset.mem_univ] using
      (intervalIntegral.integral_finsetSum
        (s := (Finset.univ : Finset (Fin p)))
        (f := fun r ξ => F (ξ + ((r : ℕ) : ℝ) / γ))
        (h := by
          intro r _hr
          exact hshift r))
  have hset_eq_interval : ∀ r : Fin p,
      (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          F (ξ + ((r : ℕ) : ℝ) / γ)) =
        ∫ ξ in (0 : ℝ)..γ⁻¹,
          F (ξ + ((r : ℕ) : ℝ) / γ) := by
    intro r
    rw [intervalIntegral.integral_of_le hγ_inv_nonneg]
  have hsum_set :
      (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          (∑ r : Fin p, F (ξ + ((r : ℕ) : ℝ) / γ))) =
        ∑ r : Fin p, ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          F (ξ + ((r : ℕ) : ℝ) / γ) := by
    calc
      (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          (∑ r : Fin p, F (ξ + ((r : ℕ) : ℝ) / γ))) =
          ∫ ξ in (0 : ℝ)..γ⁻¹,
            (∑ r : Fin p, F (ξ + ((r : ℕ) : ℝ) / γ)) := by
            rw [intervalIntegral.integral_of_le hγ_inv_nonneg]
      _ = ∑ r : Fin p, ∫ ξ in (0 : ℝ)..γ⁻¹,
            F (ξ + ((r : ℕ) : ℝ) / γ) := hsum_interval
      _ = ∑ r : Fin p, ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
            F (ξ + ((r : ℕ) : ℝ) / γ) := by
            apply Finset.sum_congr rfl
            intro r _hr
            exact (hset_eq_interval r).symm
  calc
    (∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
        (∑ r : Fin p,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2)) =
        (∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          (∑ r : Fin p, F (ξ + ((r : ℕ) : ℝ) / γ))) := by
          simp [F, γ]
    _ = ∑ r : Fin p, ∫ ξ in Set.Ioc (0 : ℝ) γ⁻¹,
          F (ξ + ((r : ℕ) : ℝ) / γ) := hsum_set
    _ = ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
          simpa [F, γ] using
            rationalPositive_frequency_partition_integral_of_memLp
              hα hβ hgap hαβ x s

/-- Concrete rational-density vector fiber field assembled from the honest
ZakTransform frequency fibers on the fundamental rectangle and extended by zero
outside it. -/
noncomputable def rationalPositiveSpecFiberField
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (_hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) → ℝ × ℝ → Fin p → ℂ := by
  classical
  exact fun x z r =>
    if z ∈ rationalPositiveFundamentalRect α p q then
      rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((r : ℕ) : ℝ) / rationalZakGamma α q)
    else 0

/-- A fixed honest rational-Zak fiber field chosen from the existence residual. -/
noncomputable def rationalPositiveFiberField
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) → ℝ × ℝ → Fin p → ℂ :=
  rationalPositiveSpecFiberField hα hβ hpq_coprime hgap hαβ

/-- Inside the rational fundamental rectangle, the chosen finite-vector field
is the corresponding shifted one-dimensional frequency fiber. -/
theorem rationalPositiveFiberField_eq_base_of_mem_rect
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∈ rationalPositiveFundamentalRect α p q) (r : Fin p) :
    rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r =
      rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((r : ℕ) : ℝ) / rationalZakGamma α q) := by
  simp [rationalPositiveFiberField, rationalPositiveSpecFiberField, hz]

/-- Outside the rational fundamental rectangle, the chosen finite-vector field
is the zero extension. -/
theorem rationalPositiveFiberField_eq_zero_of_not_mem_rect
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∉ rationalPositiveFundamentalRect α p q) (r : Fin p) :
    rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r = 0 := by
  simp [rationalPositiveFiberField, rationalPositiveSpecFiberField, hz]

/-- The default finite-function norm in Lean is the sup norm, hence its square
is controlled by the Euclidean sum of squared component norms. -/
lemma finiteVector_norm_sq_le_sum_norm_sq
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  classical
  let S : ℝ := ∑ i, ‖v i‖ ^ 2
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hcoord : ∀ i, ‖v i‖ ≤ Real.sqrt S := by
    intro i
    have hi : ‖v i‖ ^ 2 ≤ S := by
      exact Finset.single_le_sum (fun j _hj => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    have hi' : ‖v i‖ ^ 2 ≤ (Real.sqrt S) ^ 2 := by
      simpa [Real.sq_sqrt hS_nonneg] using hi
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).1 hi'
  have hnorm : ‖v‖ ≤ Real.sqrt S :=
    Zak.pi_norm_le_of_forall_norm_le v (Real.sqrt_nonneg S) hcoord
  have hsq : ‖v‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).2 hnorm
  simpa [S, Real.sq_sqrt hS_nonneg] using hsq

/-- Conversely, the Euclidean sum of squared component norms is controlled by
the finite sup norm up to the cardinality factor. -/
lemma finiteVector_sum_norm_sq_le_card_mul_norm_sq
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
  simpa [dotProduct, RCLike.norm_sq_eq_def] using
    (Zak.re_dotProduct_star_self_le_card_mul_norm_sq v)

/-- Pointwise comparison from the chosen fiber-field sup-norm to the sum of
its component squared norms. -/
lemma rationalPositiveFiberField_norm_sq_le_component_energy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) :
    ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 ≤
      ∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 :=
  finiteVector_norm_sq_le_sum_norm_sq
    (rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z)

/-- Pointwise comparison from the component squared-norm sum back to the
chosen fiber-field sup-norm, with the finite cardinality loss. -/
lemma rationalPositiveFiberField_component_energy_le_card_mul_norm_sq
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) :
    (∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) ≤
      (p : ℝ) *
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 := by
  simpa using
    (finiteVector_sum_norm_sq_le_card_mul_norm_sq
      (rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z))

/-- Upper component-energy bound for the student-corrected matrix.  It combines
the existing upper bound for `P(s,ξ)^*` with the finite Fourier row-change
estimate `‖D(ξ)^* w‖ ≤ p ‖w‖`. -/
lemma rationalPositiveCorrectedZakMatrix_upper_component_energy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {B : ℝ} (hB : 0 ≤ B)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ)
    (hupper : ∀ z w, ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2) :
    ‖rationalPositiveCorrectedZakMatrix α p q z *ᵥ
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 ≤
      (B * (p : ℝ) ^ 2) *
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by
  let v := rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z
  let D := rationalPositiveFourierRowChange α p q z
  let CE : ℝ := ∑ r : Fin p, ‖v r‖ ^ 2
  have hrewrite :
      rationalPositiveCorrectedZakMatrix α p q z *ᵥ v =
        rationalZakMatrix α p q z *ᵥ (Dᴴ *ᵥ v) := by
    simp [rationalPositiveCorrectedZakMatrix, D, Matrix.mulVec_mulVec]
  have hD :
      ‖Dᴴ *ᵥ v‖ ^ 2 ≤ (p : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    simpa [D] using
      rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_sq_le α p q z v
  have hN_le : ‖v‖ ^ 2 ≤ CE := by
    simpa [CE, v] using
      rationalPositiveFiberField_norm_sq_le_component_energy
        hα hβ hpq_coprime hgap hαβ x z
  have hD_comp :
      ‖Dᴴ *ᵥ v‖ ^ 2 ≤ (p : ℝ) ^ 2 * CE := by
    exact le_trans hD
      (mul_le_mul_of_nonneg_left hN_le (sq_nonneg (p : ℝ)))
  calc
    ‖rationalPositiveCorrectedZakMatrix α p q z *ᵥ
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
        = ‖rationalZakMatrix α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2 := by
            simp [v, hrewrite]
    _ ≤ B * ‖Dᴴ *ᵥ v‖ ^ 2 := hupper z (Dᴴ *ᵥ v)
    _ ≤ B * ((p : ℝ) ^ 2 * CE) :=
          mul_le_mul_of_nonneg_left hD_comp hB
    _ = (B * (p : ℝ) ^ 2) * CE := by ring

/-- Positivity of the student-corrected coefficient normalization
`η γ / p^2`. -/
lemma rationalPositiveCorrectedCoeffScale_pos
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    0 < rationalPositiveCorrectedCoeffScale α p q := by
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp_nat
  have hq : 0 < q := q_pos_of_gap hgap
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  unfold rationalPositiveCorrectedCoeffScale
  positivity

/-- Lower component-energy bound for the student-corrected matrix.  The new
ingredient is the uniform finite-Fourier lower bound for `D(ξ)^*`; the final
factor `1 / p` converts Lean's finite sup norm back to the summed component
energy. -/
lemma rationalPositiveCorrectedZakMatrix_lower_component_energy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ)
    (hlower : ∀ z w,
      A * ‖w‖ ^ 2 ≤ ‖rationalZakMatrix α p q z *ᵥ w‖ ^ 2)
    (hDlower : ∀ z w,
      c * ‖w‖ ^ 2 ≤
        ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ^ 2) :
    ((A * c) / (p : ℝ)) *
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) ≤
      ‖rationalPositiveCorrectedZakMatrix α p q z *ᵥ
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 := by
  let v := rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z
  let D := rationalPositiveFourierRowChange α p q z
  let CE : ℝ := ∑ r : Fin p, ‖v r‖ ^ 2
  let N : ℝ := ‖v‖ ^ 2
  have hp_nat : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp_nat
  have hAc_pos : 0 < A * c := mul_pos hA hc
  have hCE_le : CE ≤ (p : ℝ) * N := by
    simpa [CE, N, v] using
      rationalPositiveFiberField_component_energy_le_card_mul_norm_sq
        hα hβ hpq_coprime hgap hαβ x z
  have hscaled : ((A * c) / (p : ℝ)) * CE ≤ A * (c * N) := by
    have hmul : (A * c) * CE ≤ (A * c) * N * (p : ℝ) := by
      calc
        (A * c) * CE ≤ (A * c) * ((p : ℝ) * N) :=
          mul_le_mul_of_nonneg_left hCE_le hAc_pos.le
        _ = (A * c) * N * (p : ℝ) := by ring
    have hdiv : (A * c) * CE / (p : ℝ) ≤ (A * c) * N :=
      (div_le_iff₀ hp_real).2 hmul
    calc
      ((A * c) / (p : ℝ)) * CE = (A * c) * CE / (p : ℝ) := by ring
      _ ≤ (A * c) * N := hdiv
      _ = A * (c * N) := by ring
  have hD : A * (c * N) ≤ A * ‖Dᴴ *ᵥ v‖ ^ 2 := by
    have hD0 : c * N ≤ ‖Dᴴ *ᵥ v‖ ^ 2 := by
      simpa [D, N] using hDlower z v
    exact mul_le_mul_of_nonneg_left hD0 hA.le
  have hP : A * ‖Dᴴ *ᵥ v‖ ^ 2 ≤
      ‖rationalZakMatrix α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2 :=
    hlower z (Dᴴ *ᵥ v)
  have hrewrite_matrix :
      rationalPositiveCorrectedZakMatrix α p q z *ᵥ v =
        rationalZakMatrix α p q z *ᵥ (Dᴴ *ᵥ v) := by
    simp [rationalPositiveCorrectedZakMatrix, D, Matrix.mulVec_mulVec]
  calc
    ((A * c) / (p : ℝ)) * CE ≤ A * (c * N) := hscaled
    _ ≤ A * ‖Dᴴ *ᵥ v‖ ^ 2 := hD
    _ ≤ ‖rationalZakMatrix α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2 := hP
    _ = ‖rationalPositiveCorrectedZakMatrix α p q z *ᵥ v‖ ^ 2 := by
      rw [hrewrite_matrix]

/-- On the fundamental rectangle, the component squared-energy of the concrete
field is the sum of the corresponding shifted base-frequency fiber energies. -/
lemma rationalPositiveFiberField_component_energy_eq_sum_base_of_mem_rect
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∈ rationalPositiveFundamentalRect α p q) :
    (∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) =
      ∑ r : Fin p,
        ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (z.1, z.2 + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro r _hr
  rw [rationalPositiveFiberField_eq_base_of_mem_rect
    hα hβ hpq_coprime hgap hαβ x hz r]

/-- Outside the fundamental rectangle, the component squared-energy of the
concrete field is zero. -/
lemma rationalPositiveFiberField_component_energy_eq_zero_of_not_mem_rect
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∉ rationalPositiveFundamentalRect α p q) :
    (∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro r _hr
  rw [rationalPositiveFiberField_eq_zero_of_not_mem_rect
    hα hβ hpq_coprime hgap hαβ x hz r]
  simp

/-- Since the concrete field is zero off the fundamental rectangle, its global
component-energy integral is the corresponding set integral over that rectangle. -/
lemma rationalPositiveFiberField_component_energy_integral_eq_setIntegral_rect
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ z : ℝ × ℝ,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ))) =
      ∫ z in rationalPositiveFundamentalRect α p q,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ)) := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (ℝ × ℝ)))
    (s := rationalPositiveFundamentalRect α p q)
    (f := fun z : ℝ × ℝ =>
      ∑ r : Fin p,
        ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
    (by
      intro z hz
      exact rationalPositiveFiberField_component_energy_eq_zero_of_not_mem_rect
        hα hβ hpq_coprime hgap hαβ x hz)).symm

/-- Global component-energy integral reduced to the spatial integral of the
base-frequency Parseval energy. -/
lemma rationalPositiveFiberField_component_energy_integral_eq_base_iterated
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ z : ℝ × ℝ,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ))) =
      ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
  classical
  set η : ℝ := rationalZakEta α p q with hη_def
  set γ : ℝ := rationalZakGamma α q with hγ_def
  set S : Set ℝ := Set.Ioc (0 : ℝ) η
  set T : Set ℝ := Set.Ioc (0 : ℝ) γ⁻¹
  -- joint shifted component energy
  set J : ℝ × ℝ → ℝ := fun z =>
    ∑ r : Fin p, ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
      (z.1, z.2 + ((r : ℕ) : ℝ) / γ)‖ ^ 2 with hJ_def
  have hJ_int : IntegrableOn J (S ×ˢ T) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hrect : IntegrableOn J (rationalPositiveFundamentalRect α p q)
        (volume : Measure (ℝ × ℝ)) :=
      integrable_finsetSum _ (fun r _ =>
        rationalPositiveBaseFiberJoint_shift_sq_integrableOn hα hβ hgap hαβ x r)
    simpa [J, S, T, rationalPositiveFundamentalRect, Measure.volume_eq_prod, hη_def, hγ_def]
      using hrect
  have h1 : (∫ z : ℝ × ℝ,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ)))
      = ∫ z in rationalPositiveFundamentalRect α p q,
          (∑ r : Fin p,
            ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
          ∂(volume : Measure (ℝ × ℝ)) :=
    rationalPositiveFiberField_component_energy_integral_eq_setIntegral_rect
      hα hβ hpq_coprime hgap hαβ x
  have h2 : (∫ z in rationalPositiveFundamentalRect α p q,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ)))
      = ∫ z in rationalPositiveFundamentalRect α p q, J z ∂(volume : Measure (ℝ × ℝ)) := by
    refine setIntegral_congr_fun
      (measurableSet_rationalPositiveFundamentalRect α p q) ?_
    intro z hz
    exact rationalPositiveFiberField_component_energy_eq_sum_base_of_mem_rect
      hα hβ hpq_coprime hgap hαβ x hz
  have h3 : (∫ z in rationalPositiveFundamentalRect α p q, J z ∂(volume : Measure (ℝ × ℝ)))
      = ∫ s in S, ∫ ξ in T, J (s, ξ) := by
    have hprod := setIntegral_prod
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := J) (s := S) (t := T) hJ_int
    simpa [S, T, rationalPositiveFundamentalRect, Measure.volume_eq_prod, hη_def, hγ_def]
      using hprod
  have h4 : (∫ s in S, ∫ ξ in T, J (s, ξ))
      = ∫ s in S, ∫ ω in Set.Ioc (0 : ℝ) η⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [rationalPositiveBaseFiberJoint_slice_ae hα hβ hgap hαβ x]
      with s hs
    rw [← rationalPositive_frequency_partition_integral_sum_inside hα hβ hgap hαβ x s]
    refine integral_congr_ae ?_
    have hshift : ∀ r : Fin p,
        (fun ξ : ℝ => rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((r : ℕ) : ℝ) / γ))
          =ᵐ[(volume : Measure ℝ).restrict T]
        (fun ξ : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((r : ℕ) : ℝ) / γ)) := by
      intro r
      have hmp : MeasurePreserving (fun ξ : ℝ => ξ + ((r : ℕ) : ℝ) / γ)
          (volume : Measure ℝ) (volume : Measure ℝ) :=
        measurePreserving_add_right (volume : Measure ℝ) (((r : ℕ) : ℝ) / γ)
      have hmp' : MeasurePreserving (fun ξ : ℝ => ξ + ((r : ℕ) : ℝ) / γ)
          ((volume : Measure ℝ).restrict
            ((fun ξ : ℝ => ξ + ((r : ℕ) : ℝ) / γ) ⁻¹' Set.Ioc (0 : ℝ) η⁻¹))
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) η⁻¹)) :=
        hmp.restrict_preimage measurableSet_Ioc
      have hsub : T ⊆ (fun ξ : ℝ => ξ + ((r : ℕ) : ℝ) / γ) ⁻¹' Set.Ioc (0 : ℝ) η⁻¹ := by
        intro ξ hξ
        refine Set.mem_preimage.mpr ?_
        have := rationalPositive_shifted_frequency_mem_baseInterval
          hα hβ hgap hαβ r (ξ := ξ) (by simpa [T, hγ_def] using hξ)
        simpa [hη_def, hγ_def] using this
      have hcomp := hmp'.quasiMeasurePreserving.ae_eq_comp hs
      exact (hcomp.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    have hae : ∀ᵐ ξ ∂((volume : Measure ℝ).restrict T), ∀ r : Fin p,
        ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x (s, ξ + ((r : ℕ) : ℝ) / γ)‖ ^ 2
          = ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
              (ξ + ((r : ℕ) : ℝ) / γ)‖ ^ 2 := by
      rw [ae_all_iff]
      intro r
      filter_upwards [hshift r] with ξ hξ
      rw [hξ]
    have hsum : (fun ξ : ℝ => ∑ r : Fin p,
          ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x (s, ξ + ((r : ℕ) : ℝ) / γ)‖ ^ 2)
        =ᵐ[(volume : Measure ℝ).restrict T]
        (fun ξ : ℝ => ∑ r : Fin p,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((r : ℕ) : ℝ) / γ)‖ ^ 2) := by
      filter_upwards [hae] with ξ hξ
      exact Finset.sum_congr rfl (fun r _ => hξ r)
    simpa [hJ_def, hγ_def] using hsum
  rw [h1, h2, h3, h4]

/-- Global integrability of the concrete fiber component-energy, routed through
the finite nonnegative `lintegral` rectangle residual. -/
theorem rationalPositiveFiberField_component_energy_integrable_from_lintegral
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x, Integrable
      (fun z : ℝ × ℝ =>
        ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
  classical
  intro x
  let fieldEnergy : ℝ × ℝ → ℝ := fun z =>
    ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2
  have hrect : IntegrableOn fieldEnergy
      (rationalPositiveFundamentalRect α p q) (volume : Measure (ℝ × ℝ)) := by
    have hsum : IntegrableOn
        (fun z : ℝ × ℝ => ∑ r : Fin p,
          ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
            (z.1, z.2 + ((r : ℕ) : ℝ) / rationalZakGamma α q)‖ ^ 2)
        (rationalPositiveFundamentalRect α p q) (volume : Measure (ℝ × ℝ)) :=
      integrable_finsetSum _ (fun r _ =>
        rationalPositiveBaseFiberJoint_shift_sq_integrableOn hα hβ hgap hαβ x r)
    refine hsum.congr_fun ?_ (measurableSet_rationalPositiveFundamentalRect α p q)
    intro z hz
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rationalPositiveFiberField_eq_base_of_mem_rect hα hβ hpq_coprime hgap hαβ x hz r]
  have hzero : ∀ z ∉ rationalPositiveFundamentalRect α p q, fieldEnergy z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [rationalPositiveFiberField_eq_zero_of_not_mem_rect hα hβ hpq_coprime hgap hαβ x hz r]
    simp
  simpa [fieldEnergy] using hrect.integrable_of_forall_notMem_eq_zero hzero

/-- Integrability of the natural component squared-energy of the concrete
rational-Zak fiber field, now routed through the finite `lintegral` rectangle
residual. -/
theorem rationalPositiveFiberField_component_energy_integrable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x, Integrable
      (fun z : ℝ × ℝ =>
        ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) :=
  rationalPositiveFiberField_component_energy_integrable_from_lintegral
    hα hβ hpq_coprime hgap hαβ

/-- Componentwise a.e. strong measurability of the concrete rational-Zak fiber
field follows by zero-extending the shifted base-frequency fiber outside the
rational fundamental rectangle. -/
theorem rationalPositiveFiberField_component_aestronglyMeasurable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x r, AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r)
      (volume : Measure (ℝ × ℝ)) := by
  classical
  intro x r
  let S : Set (ℝ × ℝ) := rationalPositiveFundamentalRect α p q
  let f : ℝ × ℝ → ℂ := fun z =>
    rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
      (z.1, z.2 + ((r : ℕ) : ℝ) / rationalZakGamma α q)
  have hguarded :
      AEStronglyMeasurable
        (S.piecewise f (fun _ : ℝ × ℝ => (0 : ℂ)))
        (volume : Measure (ℝ × ℝ)) := by
    have hfS : AEStronglyMeasurable f
        ((volume : Measure (ℝ × ℝ)).restrict S) := by
      simpa [S, f] using
        rationalPositiveBaseFiberJoint_shift_aestronglyMeasurableOn
          hα hβ hgap hαβ x r
    have hzero : AEStronglyMeasurable (fun _ : ℝ × ℝ => (0 : ℂ))
        ((volume : Measure (ℝ × ℝ)).restrict Sᶜ) :=
      aestronglyMeasurable_const
    exact
      AEStronglyMeasurable.piecewise
        (measurableSet_rationalPositiveFundamentalRect α p q) hfS hzero
  have hfield :
      (fun z : ℝ × ℝ =>
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r) =
        S.piecewise f (fun _ : ℝ × ℝ => (0 : ℂ)) := by
    funext z
    by_cases hz : z ∈ S
    · simp [S, f, hz, rationalPositiveFiberField,
        rationalPositiveSpecFiberField]
    · simp [S, f, hz, rationalPositiveFiberField,
        rationalPositiveSpecFiberField]
  rw [hfield]
  exact hguarded

/-- A.e. strong measurability of the finite-vector rational-Zak fiber field
follows from componentwise measurability. -/
theorem rationalPositiveFiberField_aestronglyMeasurable
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x, AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z)
      (volume : Measure (ℝ × ℝ)) := by
  intro x
  exact (aemeasurable_pi_lambda _ fun r =>
    (rationalPositiveFiberField_component_aestronglyMeasurable
      hα hβ hpq_coprime hgap hαβ x r).aemeasurable).aestronglyMeasurable

/-- Scaled Parseval identity for the natural component squared-energy of the
concrete rational-Zak fiber field. This is the honest identity supplied by the
unscaled Riesz-Fischer fibers. -/
theorem rationalPositiveFiberField_component_energy_identity_scaled
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∀ x, (∫ z : ℝ × ℝ,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ))) =
      (rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2 := by
  intro x
  calc
    (∫ z : ℝ × ℝ,
        (∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        ∂(volume : Measure (ℝ × ℝ))) =
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
            ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2 := by
          exact rationalPositiveFiberField_component_energy_integral_eq_base_iterated
            hα hβ hpq_coprime hgap hαβ x
    _ = (rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2 :=
        rationalPositiveBase_component_energy_iterated_identity_scaled
          hα hβ hgap hαβ x

end LyubarskiiNes.RationalDensity
