import LeanCode.RationalDensity.RationalPositive.BaseFiberFinite

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- On summable fibers, the concrete base frequency fiber has the prescribed
interval Fourier coefficients. -/
theorem rationalPositiveBaseFrequencyFiber_fourierCoeffOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ)
    (hc : Summable fun k : ℤ =>
      ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2)
    (k : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω) k =
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) := by
  unfold rationalPositiveBaseFrequencyFiber
  simp [hc]
  exact Zak.zakL2FrequencyFiber_fourierCoeffOn (rationalZakEta α p q)
    (rationalZakEta_pos hα hβ hgap hαβ) (fun t : ℝ => x t) s hc k

/-- The concrete base frequency fiber is always an `L²` function on the
frequency interval, since it is an `Lp` element by construction. -/
theorem rationalPositiveBaseFrequencyFiber_memLp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ) :
    MemLp
      (fun ω : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω)
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) :=
  Lp.memLp (rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s)

/-- Fixed-spatial uniqueness bridge for the base frequency fiber: any
`L²((0, eta^{-1}])` representative with the same interval Fourier coefficients
as the guarded Riesz-Fischer fiber agrees with it after lifting to the
AddCircle.  This is the exact uniqueness step needed after proving the
coefficient identities for the product `L²` limit. -/
theorem rationalPositiveBaseFrequencyFiber_liftIoc_ae_eq_of_fourierCoeffOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    [Fact (0 < (rationalZakEta α p q)⁻¹ - (0 : ℝ))]
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ)
    (hc : Summable fun k : ℤ =>
      ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2)
    {F : ℝ → ℂ}
    (hF : MemLp F 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))
    (hcoeff : ∀ k : ℤ,
      fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        F k =
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))) :
    AddCircle.liftIoc ((rationalZakEta α p q)⁻¹ - (0 : ℝ)) (0 : ℝ) F
      =ᵐ[AddCircle.haarAddCircle]
    AddCircle.liftIoc ((rationalZakEta α p q)⁻¹ - (0 : ℝ)) (0 : ℝ)
      (fun ω : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω) := by
  have hF_T : MemLp F 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ)
          ((0 : ℝ) + ((rationalZakEta α p q)⁻¹ - (0 : ℝ))))) := by
    simpa [sub_zero] using hF
  have hB_T : MemLp
      (fun ω : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω)
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ)
          ((0 : ℝ) + ((rationalZakEta α p q)⁻¹ - (0 : ℝ))))) := by
    simpa [sub_zero] using
      rationalPositiveBaseFrequencyFiber_memLp hα hβ hgap hαβ x s
  refine liftIoc_ae_eq_of_fourierCoeff_eq
    (T := (rationalZakEta α p q)⁻¹ - (0 : ℝ)) (a := (0 : ℝ)) hF_T hB_T ?_
  intro k
  have hFcoeff := hcoeff k
  have hBcoeff :=
    rationalPositiveBaseFrequencyFiber_fourierCoeffOn
      hα hβ hgap hαβ x s hc k
  unfold fourierCoeffOn at hFcoeff hBcoeff
  exact hFcoeff.trans hBcoeff.symm

/-- RationalDensity-specialized Parseval identity for the concrete base frequency fiber. -/
theorem rationalPositiveBaseFrequencyFiber_parseval
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ)
    (hc : Summable fun k : ℤ =>
      ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) :
    rationalZakEta α p q *
        (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2) =
      ∑' k : ℤ,
        ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  unfold rationalPositiveBaseFrequencyFiber
  simp [hc]
  exact Zak.zakL2FrequencyFiber_parseval (rationalZakEta α p q)
    (rationalZakEta_pos hα hβ hgap hαβ) (fun t : ℝ => x t) s hc

/-- Solved-for-integral form of the fixed-spatial base-frequency Parseval
identity. This is the algebraic form needed before applying spatial
periodization. -/
theorem rationalPositiveBaseFrequencyFiber_integral_eq_inv_eta_tsum
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ)
    (hc : Summable fun k : ℤ =>
      ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) :
    (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2) =
      (rationalZakEta α p q)⁻¹ *
        ∑' k : ℤ,
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  let η : ℝ := rationalZakEta α p q
  let I : ℝ :=
    ∫ ω in Set.Ioc (0 : ℝ) η⁻¹,
      ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2
  let S : ℝ :=
    ∑' k : ℤ, ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2
  have hη : η ≠ 0 := ne_of_gt (rationalZakEta_pos hα hβ hgap hαβ)
  have hparse : η * I = S := by
    simpa [η, I, S] using
      rationalPositiveBaseFrequencyFiber_parseval hα hβ hgap hαβ x s hc
  calc
    I = η⁻¹ * (η * I) := by
      field_simp [hη]
    _ = η⁻¹ * S := by
      rw [hparse]

/-- A.e. solved-for-integral Parseval form for the concrete base-frequency
fiber. -/
theorem rationalPositiveBaseFrequencyFiber_integral_eq_inv_eta_tsum_ae
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q) →
      (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω‖ ^ 2) =
        (rationalZakEta α p q)⁻¹ *
          ∑' k : ℤ,
            ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hsummable :=
    Zak.zakFiberSampleSqSummableAETarget_of_pos (rationalZakEta α p q) hη
      (fun t : ℝ => x t) (Lp.memLp x)
  filter_upwards [hsummable] with s hs
  intro hs_mem
  exact rationalPositiveBaseFrequencyFiber_integral_eq_inv_eta_tsum
    hα hβ hgap hαβ x s (hs hs_mem)

/-- Spatial periodization of the ambient `L²` squared norm over one rational-Zak
spatial period. This is the summation input that will be paired with the
fixed-spatial Parseval identity. -/
theorem rationalPositive_spatial_sample_sq_integral_hasSum
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    HasSum
      (fun k : ℤ =>
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ‖(fun t : ℝ => x t)
            (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2)
      (∫ t : ℝ, ‖(fun u : ℝ => x u) t‖ ^ 2) := by
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hΦ :
      Integrable
        (fun t : ℝ => ‖(fun u : ℝ => x u) t‖ ^ 2)
        (volume : Measure ℝ) :=
    Zak.integrable_norm_sq_of_memLp_two (Lp.memLp x)
  simpa using
    Zak.realLineScaledPeriodizationIntervalHasSum_sub
      (rationalZakEta α p q) hη hΦ

/-- Finite tails of the spatial periodization series are uniformly small
outside a sufficiently large symmetric integer interval. -/
theorem rationalPositive_spatial_sample_sq_finite_tail_small
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ ε > 0, ∃ M : ℕ, ∀ N : ℕ,
      (∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) < ε := by
  intro ε hε
  let a : ℤ → ℝ := fun k =>
    ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
      ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2
  have hsummable : Summable a :=
    (rationalPositive_spatial_sample_sq_integral_hasSum
      hα hβ hgap hαβ x).summable
  rcases hsummable.tsum_vanishing (e := Set.Iio ε)
      (Iio_mem_nhds hε) with ⟨s0, hs0⟩
  rcases finset_int_subset_symmetric_Icc s0 with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro N
  let u : Finset ℤ :=
    Finset.Icc (-(N : ℤ)) (N : ℤ) \
      Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hu_disjoint : Disjoint (↑(u : Finset ℤ) : Set ℤ) (↑s0 : Set ℤ) := by
    rw [Set.disjoint_left]
    intro k hku hks
    have hku_fin : k ∈ u := by simpa using hku
    have hk_not : k ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
      (Finset.mem_sdiff.mp hku_fin).2
    exact hk_not (hM hks)
  have hsmall := hs0 (↑(u : Finset ℤ) : Set ℤ) hu_disjoint
  have hsmall_attach :
      (∑ b ∈ u.attach, a b) < ε := by
    simpa [a] using hsmall
  have hattach_eq : (∑ b ∈ u.attach, a b) = ∑ k ∈ u, a k := by
    rw [Finset.sum_attach]
  simpa [a, u, hattach_eq] using hsmall_attach

/-- The `L²(Q)` norm of the finite Cauchy tail tends to zero uniformly in the
outer truncation once the inner truncation is sufficiently large. -/
theorem rationalPositiveBaseFiberPartialTail_product_integral_small
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ ε > 0, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      (∫ z in Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
          Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
        ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) < ε := by
  intro ε hε
  let η : ℝ := rationalZakEta α p q
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  rcases rationalPositive_spatial_sample_sq_finite_tail_small
      hα hβ hgap hαβ x (η * ε) (mul_pos hη hε) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro N hMN
  let I : ℝ :=
    ∫ z in Set.Ioc (0 : ℝ) η ×ˢ Set.Ioc (0 : ℝ) η⁻¹,
      ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
      ∂((volume : Measure ℝ).prod (volume : Measure ℝ))
  have hscaled :
      η * I =
      ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ∫ s in Set.Ioc (0 : ℝ) η,
          ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2 := by
    simpa [I, η] using
      rationalPositiveBaseFiberPartialTail_product_parseval_sum_integral
        hα hβ hgap hαβ x M N hMN
  have htail_lt :
      (∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ∫ s in Set.Ioc (0 : ℝ) η,
          ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2) < η * ε := by
    simpa [η] using hM N
  have hmul : η * I < η * ε := by
    rwa [hscaled]
  nlinarith

/-- Real-valued `L²` norm control from a square-integral estimate. -/
theorem lpNorm_two_lt_of_integral_sq_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : (∫ x, ‖f x‖ ^ 2 ∂μ) < ε ^ 2) :
    lpNorm f 2 μ < ε := by
  have hnorm :
      lpNorm f 2 μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    simpa using
      (lpNorm_eq_integral_norm_rpow_toReal
        (p := (2 : ℝ≥0∞)) (μ := μ) (f := f)
        two_ne_zero ENNReal.ofNat_ne_top hf)
  have hI_nonneg : 0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) := by
    exact integral_nonneg fun x => by positivity
  rw [hnorm]
  rw [Real.rpow_inv_lt_iff_of_pos hI_nonneg hε.le zero_lt_two]
  simpa [Real.rpow_natCast] using hsmall

/-- Converse real-valued `L²` norm control: a small `L²` norm forces a small
square integral. -/
theorem integral_sq_lt_of_lpNorm_two_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : lpNorm f 2 μ < ε) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) < ε ^ 2 := by
  have hnorm :
      lpNorm f 2 μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    simpa using
      (lpNorm_eq_integral_norm_rpow_toReal
        (p := (2 : ENNReal)) (μ := μ) (f := f)
        two_ne_zero ENNReal.ofNat_ne_top hf)
  have hI_nonneg : 0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) := by
    exact integral_nonneg fun x => by positivity
  rw [hnorm] at hsmall
  rw [Real.rpow_inv_lt_iff_of_pos hI_nonneg hε.le zero_lt_two] at hsmall
  simpa [Real.rpow_natCast] using hsmall

/-- The finite partial sums from the student Statement 1 construction are a
Cauchy sequence in `L²((0,η] × (0,η⁻¹])`. -/
theorem rationalPositiveBaseFiberPartialSum_Lp_cauchy
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    CauchySeq (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  rcases rationalPositiveBaseFiberPartialTail_product_integral_small
      hα hβ hgap hαβ x (ε ^ 2) (sq_pos_of_pos hε) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro N hMN
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μQ : Measure (ℝ × ℝ) :=
    (((volume : Measure ℝ).restrict S).prod
      ((volume : Measure ℝ).restrict U))
  let T : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialTail α p q M N x
  have hdist :
      dist (rationalPositiveBaseFiberPartialSum_Lp α p q x N)
          (rationalPositiveBaseFiberPartialSum_Lp α p q x M) =
        lpNorm T 2 μQ := by
    simpa [T, μQ, S, U, η] using
      rationalPositiveBaseFiberPartialSum_Lp_dist_eq_lpNorm_tail α p q M N hMN x
  rw [hdist]
  have hsmall_set :
      (∫ z in S ×ˢ U, ‖T z‖ ^ 2
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) < ε ^ 2 := by
    simpa [T, S, U, η] using hM N hMN
  have hsmall_measure :
      (∫ z, ‖T z‖ ^ 2 ∂μQ) < ε ^ 2 := by
    simpa [μQ, S, U, T, Measure.prod_restrict] using hsmall_set
  exact lpNorm_two_lt_of_integral_sq_lt
    (μ := μQ) (f := T)
    (rationalPositiveBaseFiberPartialTail_memLp_product
      α p q M N hMN x).aestronglyMeasurable
    hε hsmall_measure

/-- The finite partial sums have an actual limit in the product `L²` space.
This is the completion step in `Part7_student.tex`, Statement 1. -/
theorem rationalPositiveBaseFiberPartialSum_Lp_exists_limit
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ F : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))),
      Filter.Tendsto (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
        Filter.atTop (nhds F) :=
  cauchySeq_tendsto_of_complete
    (rationalPositiveBaseFiberPartialSum_Lp_cauchy hα hβ hgap hαβ x)

/-- Fubini slice theorem for the product `L²` space used in RationalDensity: a product
`L²((0, eta] x (0, eta^-1])` function has frequency fibers in
`L²(0, eta^-1]` for a.e. spatial parameter. -/
theorem rationalPositive_product_memLp_frequency_fibers_ae
    (α : ℝ) (p q : ℕ) {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))),
      MemLp (fun ω : ℝ => F (s, ω)) 2
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
  let S : Set ℝ := Set.Ioc (0 : ℝ) (rationalZakEta α p q)
  let U : Set ℝ := Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  have hmeas_ae :
      ∀ᵐ s ∂μS, AEStronglyMeasurable (fun ω : ℝ => F (s, ω)) μU := by
    simpa [μS, μU, S, U] using hF.aestronglyMeasurable.prodMk_left
  have hsq_int : Integrable
      (fun z : ℝ × ℝ => ‖F z‖ ^ 2) (μS.prod μU) := by
    rw [← MeasureTheory.memLp_two_iff_integrable_sq_norm
      hF.aestronglyMeasurable]
    simpa [μS, μU, S, U] using hF
  have hsq_fiber :
      ∀ᵐ s ∂μS,
        Integrable (fun ω : ℝ => ‖F (s, ω)‖ ^ 2) μU := by
    simpa using hsq_int.prod_right_ae
  filter_upwards [hmeas_ae, hsq_fiber] with s hs_meas hs_int
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hs_meas]
  exact hs_int

/-- The coefficient section `s ↦ C_j(F(s, ·))` of any product `L²` function
on `(0, eta] × (0, eta^-1]` is an `L²(0, eta]` function.  This is the
bounded coefficient-extraction step from the student's Statement 1, expressed
with `fourierCoeffOn`. -/
theorem rationalPositive_product_fourierCoeffOn_section_memLp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (j : ℤ) :
    MemLp
      (fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
          (fun ω : ℝ => F (s, ω)) j)
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  let coeff : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      (fun ω : ℝ => F (s, ω)) j
  let H : ℝ × ℝ → ℂ := fun z =>
    fourier (-j) (z.2 : AddCircle η⁻¹) • F z
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  have hab : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  have hH_meas : AEStronglyMeasurable H (μS.prod μU) := by
    have hker_cont : Continuous fun z : ℝ × ℝ =>
        fourier (-j) (z.2 : AddCircle η⁻¹) := by
      exact (map_continuous (fourier (-j))).comp
        ((AddCircle.continuous_mk' η⁻¹).comp continuous_snd)
    exact hker_cont.aestronglyMeasurable.smul
      (by simpa [μS, μU, S, U, η] using hF.aestronglyMeasurable)
  let coeffInt : ℝ → ℂ := fun s => η • ∫ ω, H (s, ω) ∂μU
  have hcoeffInt_meas : AEStronglyMeasurable coeffInt μS := by
    exact (hH_meas.integral_prod_right').const_smul η
  have hcoeff_eq : coeff =ᵐ[μS] coeffInt := by
    exact Filter.Eventually.of_forall fun s => by
      have hfour :=
        fourierCoeffOn_eq_integral
          (a := (0 : ℝ)) (b := η⁻¹)
          (f := fun ω : ℝ => F (s, ω)) j hab
      calc
        coeff s =
            fourierCoeffOn
              (a := (0 : ℝ)) (b := η⁻¹) hab
              (fun ω : ℝ => F (s, ω)) j := by
              simp [coeff]
        _ = (1 / (η⁻¹ - (0 : ℝ))) •
              ∫ ω in (0 : ℝ)..η⁻¹,
                fourier (-j) (ω : AddCircle (η⁻¹ - (0 : ℝ))) • F (s, ω) := hfour
        _ = η • ∫ ω, H (s, ω) ∂μU := by
              rw [sub_zero]
              rw [one_div, inv_inv]
              rw [intervalIntegral.integral_of_le hab.le]
        _ = coeffInt s := by simp [coeffInt]
  have hcoeff_meas : AEStronglyMeasurable coeff μS :=
    hcoeffInt_meas.congr hcoeff_eq.symm
  have hsq_int : Integrable
      (fun z : ℝ × ℝ => ‖F z‖ ^ 2) (μS.prod μU) := by
    rw [← MeasureTheory.memLp_two_iff_integrable_sq_norm
      (by simpa [μS, μU, S, U, η] using hF.aestronglyMeasurable)]
    simpa [μS, μU, S, U, η] using hF
  have hinner_int : Integrable
      (fun s : ℝ => ∫ ω, ‖F (s, ω)‖ ^ 2 ∂μU) μS :=
    hsq_int.integral_prod_left
  have hbound_int : Integrable
      (fun s : ℝ => η * ∫ ω, ‖F (s, ω)‖ ^ 2 ∂μU) μS :=
    hinner_int.const_mul η
  have hpoint : (fun s : ℝ => ‖coeff s‖ ^ 2) ≤ᵐ[μS]
      fun s : ℝ => η * ∫ ω, ‖F (s, ω)‖ ^ 2 ∂μU := by
    have hslice :=
      rationalPositive_product_memLp_frequency_fibers_ae
        α p q (by simpa [μS, μU, S, U, η] using hF)
    filter_upwards [hslice] with s hs
    have h :=
      rationalPositive_fourierCoeffOn_norm_sq_le_eta_setIntegral
        hα hβ hgap hαβ (F := fun ω : ℝ => F (s, ω)) hs j
    simpa [coeff, μU, U, η] using h
  have hcoeff_sq_int : Integrable (fun s : ℝ => ‖coeff s‖ ^ 2) μS := by
    refine hbound_int.mono' (hcoeff_meas.norm.pow 2) ?_
    filter_upwards [hpoint] with s hs
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hs
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hcoeff_meas]
  exact hcoeff_sq_int

/-- Integrated norm bound for the coefficient extractor on product `L²`.
This is the operator estimate `‖C_j F‖² ≤ η ‖F‖²` used to pass coefficient
identities from finite partial sums to the completed product limit. -/
theorem rationalPositive_product_fourierCoeffOn_section_integral_norm_sq_le_eta_product
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (j : ℤ) :
    (∫ s,
      ‖fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        (fun ω : ℝ => F (s, ω)) j‖ ^ 2
      ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)))) ≤
      rationalZakEta α p q *
        (∫ z,
          ‖F z‖ ^ 2
          ∂(((volume : Measure ℝ).restrict
            (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
            ((volume : Measure ℝ).restrict
              (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  let coeff : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      (fun ω : ℝ => F (s, ω)) j
  let H : ℝ × ℝ → ℝ := fun z => ‖F z‖ ^ 2
  have hcoeff_mem :
      MemLp coeff 2 μS := by
    simpa [coeff, μS, S, η] using
      rationalPositive_product_fourierCoeffOn_section_memLp
        hα hβ hgap hαβ hF j
  have hcoeff_int : Integrable (fun s : ℝ => ‖coeff s‖ ^ 2) μS := by
    rw [← MeasureTheory.memLp_two_iff_integrable_sq_norm
      hcoeff_mem.aestronglyMeasurable]
    exact hcoeff_mem
  have hH_int : Integrable H (μS.prod μU) := by
    rw [← MeasureTheory.memLp_two_iff_integrable_sq_norm
      (by simpa [μS, μU, S, U, η] using hF.aestronglyMeasurable)]
    simpa [H, μS, μU, S, U, η] using hF
  have hinner_int : Integrable (fun s : ℝ => ∫ ω, H (s, ω) ∂μU) μS :=
    hH_int.integral_prod_left
  have hbound_int : Integrable
      (fun s : ℝ => η * ∫ ω, H (s, ω) ∂μU) μS :=
    hinner_int.const_mul η
  have hpoint : (fun s : ℝ => ‖coeff s‖ ^ 2) ≤ᵐ[μS]
      fun s : ℝ => η * ∫ ω, H (s, ω) ∂μU := by
    have hslice :=
      rationalPositive_product_memLp_frequency_fibers_ae
        α p q (by simpa [μS, μU, S, U, η] using hF)
    filter_upwards [hslice] with s hs
    have h :=
      rationalPositive_fourierCoeffOn_norm_sq_le_eta_setIntegral
        hα hβ hgap hαβ (F := fun ω : ℝ => F (s, ω)) hs j
    simpa [coeff, H, μU, U, η] using h
  have hle := integral_mono_ae hcoeff_int hbound_int hpoint
  have hprod :
      (∫ z, H z ∂(μS.prod μU)) =
        ∫ s, ∫ ω, H (s, ω) ∂μU ∂μS := by
    exact integral_prod H hH_int
  calc
    (∫ s,
      ‖fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        (fun ω : ℝ => F (s, ω)) j‖ ^ 2
      ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)))) =
        ∫ s, ‖coeff s‖ ^ 2 ∂μS := by
          simp [coeff, μS, S, η]
    _ ≤ ∫ s, η * (∫ ω, H (s, ω) ∂μU) ∂μS := hle
    _ = η * (∫ s, ∫ ω, H (s, ω) ∂μU ∂μS) := by
          rw [MeasureTheory.integral_const_mul]
    _ = η * (∫ z, H z ∂(μS.prod μU)) := by rw [hprod]
    _ = rationalZakEta α p q *
        (∫ z,
          ‖F z‖ ^ 2
          ∂(((volume : Measure ℝ).restrict
            (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
            ((volume : Measure ℝ).restrict
              (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))) := by
          simp [H, μS, μU, S, U, η]

/-- The abstract coefficient extractor, bundled as an `L²(0, eta]` element,
for a product `L²((0, eta] × (0, eta^-1])` class. -/
noncomputable def rationalPositiveProductFourierCoeffOnSection_Lp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (F : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (j : ℤ) :
    Lp ℂ 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) :=
  (rationalPositive_product_fourierCoeffOn_section_memLp
    hα hβ hgap hαβ (Lp.memLp F) j).toLp
    (fun s : ℝ =>
      fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        (fun ω : ℝ => F (s, ω)) j)

/-- Fubini form of product a.e. equality on the RationalDensity product rectangle: if two
joint representatives agree a.e. on `(0, eta] x (0, eta^-1]`, then their
frequency slices agree a.e. for a.e. spatial parameter. -/
theorem rationalPositive_product_ae_eq_frequency_fibers_ae
    (α : ℝ) (p q : ℕ) {F G : ℝ × ℝ → ℂ}
    (hFG : F =ᵐ[
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))] G) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))),
      (fun ω : ℝ => F (s, ω)) =ᵐ[
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))]
        fun ω : ℝ => G (s, ω) := by
  let S : Set ℝ := Set.Ioc (0 : ℝ) (rationalZakEta α p q)
  let U : Set ℝ := Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  have hslice :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod (μ := μS) (ν := μU) hFG
  filter_upwards [hslice] with s hs
  change Function.curry F s =ᵐ[μU] Function.curry G s
  exact hs

/-- Compatibility between the old finite coefficient-section object and the
new abstract coefficient extractor applied to the finite product `Lp` partial
sum. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_Lp_eq_product_section
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ) :
    rationalPositiveBaseFiberPartialSum_coeffSection_Lp
      hα hβ hgap hαβ x N j =
    rationalPositiveProductFourierCoeffOnSection_Lp
      hα hβ hgap hαβ
      (rationalPositiveBaseFiberPartialSum_Lp α p q x N) j := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  let FN : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialSum α p q N x
  let FN_Lp : Lp ℂ 2 (μS.prod μU) :=
    rationalPositiveBaseFiberPartialSum_Lp α p q x N
  have hFN_mem : MemLp FN 2 (μS.prod μU) := by
    simpa [FN, μS, μU, S, U, η] using
      rationalPositiveBaseFiberPartialSum_memLp_product α p q N x
  have hcoe : (fun z : ℝ × ℝ => FN_Lp z) =ᵐ[μS.prod μU] FN := by
    simpa [FN_Lp, FN, μS, μU, S, U, η,
      rationalPositiveBaseFiberPartialSum_Lp] using hFN_mem.coeFn_toLp
  have hslice := rationalPositive_product_ae_eq_frequency_fibers_ae α p q hcoe
  have hcoeff_ae :
      (fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := η⁻¹)
          (show (0 : ℝ) < η⁻¹ from by
            have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
            exact inv_pos.mpr hη)
          (fun ω : ℝ => FN (s, ω)) j)
        =ᵐ[μS]
      fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := η⁻¹)
          (show (0 : ℝ) < η⁻¹ from by
            have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
            exact inv_pos.mpr hη)
          (fun ω : ℝ => FN_Lp (s, ω)) j := by
    filter_upwards [hslice] with s hs
    exact congrFun (fourierCoeffOn_congr_ae
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη) hs.symm) j
  unfold rationalPositiveBaseFiberPartialSum_coeffSection_Lp
    rationalPositiveProductFourierCoeffOnSection_Lp
  exact
    (rationalPositiveBaseFiberPartialSum_coeffSection_memLp
      hα hβ hgap hαβ x N j).toLp_congr
      (rationalPositive_product_fourierCoeffOn_section_memLp
        hα hβ hgap hαβ
        (Lp.memLp (rationalPositiveBaseFiberPartialSum_Lp α p q x N)) j)
      (by simpa [FN, FN_Lp, μS, S, η] using hcoeff_ae)

/-- The abstract product coefficient extractor is additive with respect to
subtraction.  This is the `Lp`-level linearity input for proving continuity of
the coefficient extractor from the student's boundedness estimate. -/
theorem rationalPositiveProductFourierCoeffOnSection_Lp_sub
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (F G : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (j : ℤ) :
    rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ (F - G) j =
      rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ F j -
        rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ G j := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  let coeffSub : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      (fun ω : ℝ => (F - G) (s, ω)) j
  let coeffF : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      (fun ω : ℝ => F (s, ω)) j
  let coeffG : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      (fun ω : ℝ => G (s, ω)) j
  have hFslice := rationalPositive_product_memLp_frequency_fibers_ae
    α p q (Lp.memLp F)
  have hGslice := rationalPositive_product_memLp_frequency_fibers_ae
    α p q (Lp.memLp G)
  have hcoe := rationalPositive_product_ae_eq_frequency_fibers_ae
    α p q (Lp.coeFn_sub F G)
  have hcoeff_ae : coeffSub =ᵐ[μS] coeffF - coeffG := by
    filter_upwards [hFslice, hGslice, hcoe] with s hFs hGs hsub
    have hcongr := congrFun (fourierCoeffOn_congr_ae
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη) hsub) j
    have hlin := rationalPositive_fourierCoeffOn_sub
      (show (0 : ℝ) < η⁻¹ from by
        have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
        exact inv_pos.mpr hη)
      hFs hGs j
    calc
      coeffSub s =
          fourierCoeffOn
            (show (0 : ℝ) < η⁻¹ from by
              have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
              exact inv_pos.mpr hη)
            (fun x : ℝ => F (s, x) - G (s, x)) j := by
            simpa [coeffSub] using hcongr
      _ = coeffF s - coeffG s := by
            simpa [coeffF, coeffG] using hlin
      _ = (coeffF - coeffG) s := rfl
  unfold rationalPositiveProductFourierCoeffOnSection_Lp
  rw [← (rationalPositive_product_fourierCoeffOn_section_memLp
    hα hβ hgap hαβ (Lp.memLp F) j).toLp_sub
    (rationalPositive_product_fourierCoeffOn_section_memLp
      hα hβ hgap hαβ (Lp.memLp G) j)]
  exact
    (rationalPositive_product_fourierCoeffOn_section_memLp
      hα hβ hgap hαβ (Lp.memLp (F - G)) j).toLp_congr
      ((rationalPositive_product_fourierCoeffOn_section_memLp
        hα hβ hgap hαβ (Lp.memLp F) j).sub
        (rationalPositive_product_fourierCoeffOn_section_memLp
          hα hβ hgap hαβ (Lp.memLp G) j))
      (by simpa [coeffSub, coeffF, coeffG, μS, S, η] using hcoeff_ae)

/-- The abstract product coefficient extractor is continuous along `L²`
limits.  This is the formal boundedness step in the student's
Riesz--Fischer fiber identification. -/
theorem rationalPositiveProductFourierCoeffOnSection_Lp_tendsto
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (Fseq : ℕ → Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (G : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (hlim : Filter.Tendsto Fseq Filter.atTop (nhds G))
    (j : ℤ) :
    Filter.Tendsto
      (fun N : ℕ =>
        rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ (Fseq N) j)
      Filter.atTop
      (nhds (rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ G j)) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μU : Measure ℝ := (volume : Measure ℝ).restrict U
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  have hη1 : 0 < η + 1 := by linarith
  let δ : ℝ := ε / (η + 1)
  have hδ : 0 < δ := div_pos hε hη1
  have hsmall_event := (Metric.tendsto_nhds.mp hlim δ hδ)
  filter_upwards [hsmall_event] with N hN
  let D : Lp ℂ 2 (μS.prod μU) := Fseq N - G
  let coeffD : ℝ → ℂ := fun s =>
    fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹)
      (show (0 : ℝ) < η⁻¹ from inv_pos.mpr hη)
      (fun ω : ℝ => D (s, ω)) j
  have hsec_sub := rationalPositiveProductFourierCoeffOnSection_Lp_sub
    hα hβ hgap hαβ (Fseq N) G j
  have hdist_sec :
      dist
        (rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ (Fseq N) j)
        (rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ G j) =
        lpNorm coeffD 2 μS := by
    rw [dist_eq_norm]
    rw [← hsec_sub]
    unfold rationalPositiveProductFourierCoeffOnSection_Lp
    rw [Lp.norm_toLp]
    exact toReal_eLpNorm
      (rationalPositive_product_fourierCoeffOn_section_memLp
        hα hβ hgap hαβ (Lp.memLp D) j).aestronglyMeasurable
  rw [hdist_sec]
  have hdist_prod :
      lpNorm (fun z : ℝ × ℝ => D z) 2 (μS.prod μU) < δ := by
    have hdist_eq :
        dist (Fseq N) G = lpNorm (fun z : ℝ × ℝ => D z) 2 (μS.prod μU) := by
      rw [dist_eq_norm]
      dsimp [D]
      rw [Lp.norm_def]
      exact toReal_eLpNorm (Lp.aestronglyMeasurable (Fseq N - G))
    simpa [hdist_eq] using hN
  have hD_int_lt :
      (∫ z, ‖D z‖ ^ 2 ∂(μS.prod μU)) < δ ^ 2 :=
    integral_sq_lt_of_lpNorm_two_lt
      (Lp.aestronglyMeasurable D) hδ hdist_prod
  have hcoeff_le :=
    rationalPositive_product_fourierCoeffOn_section_integral_norm_sq_le_eta_product
      hα hβ hgap hαβ (Lp.memLp D) j
  have hcoeff_int_lt :
      (∫ s, ‖coeffD s‖ ^ 2 ∂μS) < ε ^ 2 := by
    have hmul_lt : η * (∫ z, ‖D z‖ ^ 2 ∂(μS.prod μU)) < ε ^ 2 := by
      have hlt_delta : η * (δ ^ 2) < ε ^ 2 := by
        have hsqpos : 0 < (η + 1) ^ 2 := sq_pos_of_pos hη1
        have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
        have hratio : η / (η + 1) ^ 2 < 1 := by
          rw [div_lt_one hsqpos]
          nlinarith [sq_nonneg η]
        dsimp [δ]
        rw [div_pow]
        calc
          η * (ε ^ 2 / (η + 1) ^ 2) =
              (η / (η + 1) ^ 2) * ε ^ 2 := by ring
          _ < 1 * ε ^ 2 := mul_lt_mul_of_pos_right hratio hεsq_pos
          _ = ε ^ 2 := by ring
      exact lt_trans (mul_lt_mul_of_pos_left hD_int_lt hη) hlt_delta
    exact lt_of_le_of_lt (by simpa [coeffD, D, μS, μU, S, U, η] using hcoeff_le) hmul_lt
  exact lpNorm_two_lt_of_integral_sq_lt
    (μ := μS) (f := coeffD)
    (rationalPositive_product_fourierCoeffOn_section_memLp
      hα hβ hgap hαβ (Lp.memLp D) j).aestronglyMeasurable
    hε hcoeff_int_lt

/-- If the finite base partial sums converge in the product `L²` space to
`G`, then the product coefficient-section of `G` is the stabilized shifted
sample.  This is the formal uniqueness-of-`L²`-limits step in the student's
Statement 1 proof. -/
theorem rationalPositiveBaseFiberPartialSum_product_limit_coeffSection_eq_sample
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (G : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (hG : Filter.Tendsto
      (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      Filter.atTop (nhds G))
    (j : ℤ) :
    rationalPositiveProductFourierCoeffOnSection_Lp hα hβ hgap hαβ G j =
      rationalPositiveBaseFiberShiftedSample_Lp α p q x j := by
  have hprod :=
    rationalPositiveProductFourierCoeffOnSection_Lp_tendsto
      hα hβ hgap hαβ
      (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      G hG j
  have hprod_sections :
      Filter.Tendsto
        (fun N : ℕ =>
          rationalPositiveBaseFiberPartialSum_coeffSection_Lp
            hα hβ hgap hαβ x N j)
        Filter.atTop
        (nhds (rationalPositiveProductFourierCoeffOnSection_Lp
          hα hβ hgap hαβ G j)) :=
    hprod.congr fun N =>
      (rationalPositiveBaseFiberPartialSum_coeffSection_Lp_eq_product_section
        hα hβ hgap hαβ x N j).symm
  have hsample :=
    rationalPositiveBaseFiberPartialSum_coeffSection_Lp_tendsto_sample
      hα hβ hgap hαβ x j
  exact tendsto_nhds_unique hprod_sections hsample

/-- For a completed product `L²` limit `G`, all Fourier coefficients of
almost every frequency slice are the stabilized shifted samples.  This is the
simultaneous-countable version of the coefficient identity needed for
fiberwise Fourier uniqueness. -/
theorem rationalPositiveBaseFiberPartialSum_product_limit_coefficients_ae
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (G : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (hG : Filter.Tendsto
      (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      Filter.atTop (nhds G)) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))),
      ∀ j : ℤ,
        fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
          (fun ω : ℝ => G (s, ω)) j =
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  have hforall : ∀ j : ℤ,
      ∀ᵐ s ∂μS,
        fourierCoeffOn
          (a := (0 : ℝ)) (b := η⁻¹)
          (show (0 : ℝ) < η⁻¹ from by
            have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
            exact inv_pos.mpr hη)
          (fun ω : ℝ => G (s, ω)) j =
        (fun t : ℝ => x t) (s - η * (j : ℝ)) := by
    intro j
    have hEq :=
      rationalPositiveBaseFiberPartialSum_product_limit_coeffSection_eq_sample
        hα hβ hgap hαβ x G hG j
    have hLpAe :=
      Lp.ext_iff.mp hEq
    have hLeft :
        (fun s : ℝ =>
          rationalPositiveProductFourierCoeffOnSection_Lp
            hα hβ hgap hαβ G j s)
          =ᵐ[μS]
        (fun s : ℝ =>
          fourierCoeffOn
            (a := (0 : ℝ)) (b := η⁻¹)
            (show (0 : ℝ) < η⁻¹ from by
              have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
              exact inv_pos.mpr hη)
            (fun ω : ℝ => G (s, ω)) j) := by
      simpa [rationalPositiveProductFourierCoeffOnSection_Lp, μS, S, η] using
        (rationalPositive_product_fourierCoeffOn_section_memLp
          hα hβ hgap hαβ (Lp.memLp G) j).coeFn_toLp
    have hRight :
        (fun s : ℝ => rationalPositiveBaseFiberShiftedSample_Lp α p q x j s)
          =ᵐ[μS]
        (fun s : ℝ => (fun t : ℝ => x t) (s - η * (j : ℝ))) := by
      simpa [rationalPositiveBaseFiberShiftedSample_Lp, μS, S, η] using
        (rationalPositiveBaseFiberShiftedSample_memLp α p q x j).coeFn_toLp
    exact hLeft.symm.trans (hLpAe.trans hRight)
  exact ae_all_iff.mpr hforall

/-- The completed product `L²` limit has, for almost every spatial parameter,
the same lifted frequency slice as the guarded base frequency fiber.  This
combines the simultaneous coefficient identity with Fourier uniqueness on the
interval. -/
theorem rationalPositiveBaseFiberPartialSum_product_limit_slice_liftIoc_ae_eq_base
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    [Fact (0 < (rationalZakEta α p q)⁻¹ - (0 : ℝ))]
    (x : Lp ℂ 2 (volume : Measure ℝ))
    (G : Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))))
    (hG : Filter.Tendsto
      (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      Filter.atTop (nhds G)) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))),
      AddCircle.liftIoc ((rationalZakEta α p q)⁻¹ - (0 : ℝ)) (0 : ℝ)
          (fun ω : ℝ => G (s, ω))
        =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc ((rationalZakEta α p q)⁻¹ - (0 : ℝ)) (0 : ℝ)
          (fun ω : ℝ =>
            rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  have hslice :=
    rationalPositive_product_memLp_frequency_fibers_ae α p q (Lp.memLp G)
  have hcoeff :=
    rationalPositiveBaseFiberPartialSum_product_limit_coefficients_ae
      hα hβ hgap hαβ x G hG
  filter_upwards [hslice, hcoeff] with s hs hcoeffs
  have hsumm_coeff :
      Summable fun k : ℤ =>
        ‖fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr hη)
          (fun ω : ℝ => G (s, ω)) k‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr hη) hs).summable
  have hsumm_sample :
      Summable fun k : ℤ =>
        ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
    have hfun :
        (fun k : ℤ =>
          ‖fourierCoeffOn
            (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
            (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
              inv_pos.mpr hη)
            (fun ω : ℝ => G (s, ω)) k‖ ^ 2) =
        (fun k : ℤ =>
          ‖(fun t : ℝ => x t)
            (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2) := by
      funext k
      rw [hcoeffs k]
    simpa [hfun] using hsumm_coeff
  exact
    rationalPositiveBaseFrequencyFiber_liftIoc_ae_eq_of_fourierCoeffOn
      hα hβ hgap hαβ x s hsumm_sample hs hcoeffs

/-- Reverse direction of the lifted-interval transfer: if two lifted-interval
functions agree a.e. on the additive circle, then the original functions agree
a.e. on the fundamental interval `(a, a+T]`. -/
theorem liftIoc_ae_eq_imp_ae_eq_restrict {T a : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}
    (h : AddCircle.liftIoc T a f =ᵐ[AddCircle.haarAddCircle] AddCircle.liftIoc T a g) :
    f =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc a (a + T))] g := by
  have hmp : MeasurePreserving (((↑) : ℝ → AddCircle T))
      ((volume : Measure ℝ).restrict (Set.Ioc a (a + T)))
      (volume : Measure (AddCircle T)) :=
    AddCircle.measurePreserving_mk T a
  have hvol : AddCircle.liftIoc T a f
      =ᵐ[(volume : Measure (AddCircle T))] AddCircle.liftIoc T a g := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have hpull : (AddCircle.liftIoc T a f ∘ ((↑) : ℝ → AddCircle T))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc a (a + T))]
      (AddCircle.liftIoc T a g ∘ ((↑) : ℝ → AddCircle T)) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hvol
  have hf : (AddCircle.liftIoc T a f ∘ ((↑) : ℝ → AddCircle T))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc a (a + T))] f := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioc a (a + T), self_mem_ae_restrict measurableSet_Ioc,
      fun x hx => AddCircle.liftIoc_coe_apply hx⟩
  have hg : (AddCircle.liftIoc T a g ∘ ((↑) : ℝ → AddCircle T))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc a (a + T))] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioc a (a + T), self_mem_ae_restrict measurableSet_Ioc,
      fun x hx => AddCircle.liftIoc_coe_apply hx⟩
  exact hf.symm.trans (hpull.trans hg)

/-- The chosen product-`L²` limit of the finite base partial sums, as a single
`Lp` element on the product rectangle. -/
noncomputable def rationalPositiveBaseFiberLimit
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2
      (((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹))) :=
  (rationalPositiveBaseFiberPartialSum_Lp_exists_limit hα hβ hgap hαβ x).choose

theorem rationalPositiveBaseFiberLimit_tendsto
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun N : ℕ => rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      Filter.atTop (nhds (rationalPositiveBaseFiberLimit hα hβ hgap hαβ x)) :=
  (rationalPositiveBaseFiberPartialSum_Lp_exists_limit hα hβ hgap hαβ x).choose_spec

/-- The jointly (a.e. strongly) measurable base frequency fiber: the pointwise
representative of the product-`L²` limit. -/
noncomputable def rationalPositiveBaseFiberJoint
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) : ℝ × ℝ → ℂ :=
  fun z => rationalPositiveBaseFiberLimit hα hβ hgap hαβ x z

/-- Joint a.e. strong measurability of the limit fiber on the product rectangle. -/
theorem rationalPositiveBaseFiberJoint_aestronglyMeasurable
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (rationalPositiveBaseFiberJoint hα hβ hgap hαβ x)
      (((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹))) :=
  Lp.aestronglyMeasurable _

/-- For a.e. spatial point, the limit-fiber slice agrees a.e. with the literal
guarded base frequency fiber. -/
theorem rationalPositiveBaseFiberJoint_slice_ae
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q))),
      (fun ω : ℝ => rationalPositiveBaseFiberJoint hα hβ hgap hαβ x (s, ω))
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹)]
      (fun ω : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω) := by
  haveI : Fact (0 < (rationalZakEta α p q)⁻¹ - (0:ℝ)) :=
    ⟨by rw [sub_zero]; exact inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ)⟩
  have hslice := rationalPositiveBaseFiberPartialSum_product_limit_slice_liftIoc_ae_eq_base
    hα hβ hgap hαβ x (rationalPositiveBaseFiberLimit hα hβ hgap hαβ x)
    (rationalPositiveBaseFiberLimit_tendsto hα hβ hgap hαβ x)
  filter_upwards [hslice] with s hs
  have hres := liftIoc_ae_eq_imp_ae_eq_restrict
    (T := (rationalZakEta α p q)⁻¹ - 0) (a := 0) hs
  simpa [rationalPositiveBaseFiberJoint] using hres

/-- The product slice measure equals the restriction of `volume` to the rectangle. -/
theorem prod_restrict_eq_volume_restrict (α : ℝ) (p q : ℕ) :
    ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹))
      = (volume : Measure (ℝ × ℝ)).restrict
          (Set.Ioc (0:ℝ) (rationalZakEta α p q) ×ˢ
            Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]

/-- Joint a.e. strong measurability of the limit fiber, on `volume.restrict Q`. -/
theorem rationalPositiveBaseFiberJoint_aestronglyMeasurableOn_rect
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (rationalPositiveBaseFiberJoint hα hβ hgap hαβ x)
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0:ℝ) (rationalZakEta α p q) ×ˢ
          Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹)) := by
  rw [← prod_restrict_eq_volume_restrict]
  exact rationalPositiveBaseFiberJoint_aestronglyMeasurable hα hβ hgap hαβ x

/-- The squared norm of the limit fiber is integrable on `Q` (an honest `L²` element). -/
theorem rationalPositiveBaseFiberJoint_sq_integrableOn_rect
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun z : ℝ × ℝ => ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x z‖ ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0:ℝ) (rationalZakEta α p q) ×ˢ
          Set.Ioc (0:ℝ) (rationalZakEta α p q)⁻¹)) := by
  rw [← prod_restrict_eq_volume_restrict]
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp
    (Lp.memLp (rationalPositiveBaseFiberLimit hα hβ hgap hαβ x))

/-- Shifted joint fiber is a.e. strongly measurable on the rational rectangle. -/
theorem rationalPositiveBaseFiberJoint_shift_aestronglyMeasurableOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (r : Fin p) :
    AEStronglyMeasurable
      (fun z : ℝ × ℝ => rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((r:ℕ):ℝ) / rationalZakGamma α q))
      ((volume : Measure (ℝ × ℝ)).restrict (rationalPositiveFundamentalRect α p q)) := by
  set η : ℝ := rationalZakEta α p q with hη_def
  set c : ℝ := ((r:ℕ):ℝ) / rationalZakGamma α q with hc_def
  set Q : Set (ℝ × ℝ) := Set.Ioc (0:ℝ) η ×ˢ Set.Ioc (0:ℝ) η⁻¹ with hQ_def
  set g : ℝ × ℝ → ℂ := rationalPositiveBaseFiberJoint hα hβ hgap hαβ x with hg_def
  set φ : ℝ × ℝ → ℝ × ℝ := fun z => z + (0, c) with hφ_def
  have hQmeas : MeasurableSet Q := measurableSet_Ioc.prod measurableSet_Ioc
  have hmp : MeasurePreserving φ (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
    measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (0, c)
  have hmp' : MeasurePreserving φ
      ((volume : Measure (ℝ × ℝ)).restrict (φ ⁻¹' Q))
      ((volume : Measure (ℝ × ℝ)).restrict Q) := hmp.restrict_preimage hQmeas
  have hg' : AEStronglyMeasurable g ((volume : Measure (ℝ × ℝ)).restrict Q) :=
    rationalPositiveBaseFiberJoint_aestronglyMeasurableOn_rect hα hβ hgap hαβ x
  have hcomp : AEStronglyMeasurable (g ∘ φ)
      ((volume : Measure (ℝ × ℝ)).restrict (φ ⁻¹' Q)) :=
    hg'.comp_quasiMeasurePreserving hmp'.quasiMeasurePreserving
  have hsub : rationalPositiveFundamentalRect α p q ⊆ φ ⁻¹' Q := by
    intro z hz
    rw [rationalPositiveFundamentalRect] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hfreq := rationalPositive_shifted_frequency_mem_baseInterval
      hα hβ hgap hαβ r (ξ := z.2) hz2
    refine Set.mem_preimage.mpr ?_
    rw [hQ_def, Set.mem_prod]
    exact ⟨by simpa [hφ_def] using hz1, by simpa [hφ_def, hc_def, hη_def] using hfreq⟩
  have hle : (volume : Measure (ℝ × ℝ)).restrict (rationalPositiveFundamentalRect α p q)
      ≤ (volume : Measure (ℝ × ℝ)).restrict (φ ⁻¹' Q) := Measure.restrict_mono hsub le_rfl
  have hfin := hcomp.mono_measure hle
  have hfun : (fun z : ℝ × ℝ => g (z.1, z.2 + c)) = g ∘ φ := by
    funext z; simp only [Function.comp_def, hφ_def]; congr 1; simp [Prod.ext_iff]
  rw [hfun]; exact hfin

/-- The squared norm of the shifted joint fiber is integrable on the rectangle. -/
theorem rationalPositiveBaseFiberJoint_shift_sq_integrableOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (r : Fin p) :
    IntegrableOn
      (fun z : ℝ × ℝ => ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((r:ℕ):ℝ) / rationalZakGamma α q)‖ ^ 2)
      (rationalPositiveFundamentalRect α p q) (volume : Measure (ℝ × ℝ)) := by
  set η : ℝ := rationalZakEta α p q with hη_def
  set c : ℝ := ((r:ℕ):ℝ) / rationalZakGamma α q with hc_def
  set Q : Set (ℝ × ℝ) := Set.Ioc (0:ℝ) η ×ˢ Set.Ioc (0:ℝ) η⁻¹ with hQ_def
  set g : ℝ × ℝ → ℝ :=
    fun z => ‖rationalPositiveBaseFiberJoint hα hβ hgap hαβ x z‖ ^ 2 with hg_def
  set φ : ℝ × ℝ → ℝ × ℝ := fun z => z + (0, c) with hφ_def
  have hmp : MeasurePreserving φ (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
    measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (0, c)
  have hg_int : Integrable g ((volume : Measure (ℝ × ℝ)).restrict Q) :=
    rationalPositiveBaseFiberJoint_sq_integrableOn_rect hα hβ hgap hαβ x
  have hemb : MeasurableEmbedding φ := by
    rw [hφ_def]; exact (MeasurableEquiv.addRight ((0:ℝ), c)).measurableEmbedding
  have hcomp : Integrable (g ∘ φ)
      ((volume : Measure (ℝ × ℝ)).restrict (φ ⁻¹' Q)) :=
    (hmp.integrableOn_comp_preimage hemb).mpr hg_int
  have hsub : rationalPositiveFundamentalRect α p q ⊆ φ ⁻¹' Q := by
    intro z hz
    rw [rationalPositiveFundamentalRect] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hfreq := rationalPositive_shifted_frequency_mem_baseInterval
      hα hβ hgap hαβ r (ξ := z.2) hz2
    refine Set.mem_preimage.mpr ?_
    rw [hQ_def, Set.mem_prod]
    exact ⟨by simpa [hφ_def] using hz1, by simpa [hφ_def, hc_def, hη_def] using hfreq⟩
  have hle : (volume : Measure (ℝ × ℝ)).restrict (rationalPositiveFundamentalRect α p q)
      ≤ (volume : Measure (ℝ × ℝ)).restrict (φ ⁻¹' Q) := Measure.restrict_mono hsub le_rfl
  have hfin := hcomp.mono_measure hle
  have hfun : (fun z : ℝ × ℝ => g (z.1, z.2 + c)) = g ∘ φ := by
    funext z; simp only [Function.comp_def, hφ_def]; congr 1; simp [Prod.ext_iff]
  rw [IntegrableOn]
  show Integrable (fun z : ℝ × ℝ => g (z.1, z.2 + c))
    ((volume : Measure (ℝ × ℝ)).restrict (rationalPositiveFundamentalRect α p q))
  rw [hfun]; exact hfin

end LyubarskiiNes.RationalDensity
