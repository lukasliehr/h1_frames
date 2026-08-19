import LeanCode.RationalDensity.RationalPositive.GaussianPoisson

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

/-- Fundamental rectangle for the concrete rational-density fiber field. -/
def rationalPositiveFundamentalRect (α : ℝ) (p q : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
    Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹

/-- The rational Zak fundamental rectangle is measurable. -/
lemma measurableSet_rationalPositiveFundamentalRect (α : ℝ) (p q : ℕ) :
    MeasurableSet (rationalPositiveFundamentalRect α p q) := by
  unfold rationalPositiveFundamentalRect
  exact measurableSet_Ioc.prod measurableSet_Ioc

/-- Student Step 4 interval geometry: on the short frequency interval
`(0, gamma^{-1}]`, the shifted frequency `xi + r / gamma` lies in the full
base-frequency interval `(0, eta^{-1}]`. -/
lemma rationalPositive_shifted_frequency_mem_baseInterval
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (r : Fin p) {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹) :
    ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q ∈
      Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹ := by
  let γ : ℝ := rationalZakGamma α q
  have hγ : 0 < γ := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  constructor
  · have hr_nonneg : 0 ≤ ((r : ℕ) : ℝ) / γ := by positivity
    linarith [hξ.1]
  · have hnum : ((r : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt r.2
    calc
      ξ + ((r : ℕ) : ℝ) / rationalZakGamma α q
          ≤ γ⁻¹ + ((r : ℕ) : ℝ) / γ := by
            simpa [γ] using add_le_add_right hξ.2 (((r : ℕ) : ℝ) / γ)
      _ = (((r : ℕ) : ℝ) + 1) / γ := by
            rw [inv_eq_one_div]
            ring
      _ ≤ (p : ℝ) / γ := div_le_div_of_nonneg_right hnum hγ.le
      _ = (rationalZakEta α p q)⁻¹ := by
            simpa [γ] using
              (rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ).symm

/-- Base one-dimensional frequency fiber built from the honest ZakTransform
Riesz-Fischer `L²` Zak fiber. If the required sample-square summability is not
available at the point, the guarded definition returns the zero `Lp` element. -/
noncomputable def rationalPositiveBaseFrequencyFiber
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) :
    Lp ℂ 2 ((volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
  let η : ℝ := rationalZakEta α p q
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  by_cases hc : Summable fun k : ℤ => ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2
  · exact Zak.zakL2FrequencyFiber η hη (fun t : ℝ => x t) s hc
  · exact 0

/-- Finite Fourier partial sums from `Part7_student.tex`, Statement 1.  These
are the elementary jointly measurable approximants to the eventual honest
fiber field on `(0,η] × (0,η⁻¹]`. -/
noncomputable def rationalPositiveBaseFiberPartialSum
    (α : ℝ) (p q N : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ℝ × ℝ → ℂ :=
  fun z =>
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (fun t : ℝ => x t) (z.1 - rationalZakEta α p q * (k : ℝ)) *
        Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
          ((rationalZakEta α p q : ℂ) * (k : ℂ) * (z.2 : ℂ)))

/-- The finite tail `F_N - F_M` from the student's Cauchy estimate, expressed
as the symmetric interval `[-N,N]` with the inner interval `[-M,M]` removed. -/
noncomputable def rationalPositiveBaseFiberPartialTail
    (α : ℝ) (p q M N : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    ℝ × ℝ → ℂ :=
  fun z =>
    ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
        Finset.Icc (-(M : ℤ)) (M : ℤ)),
      (fun t : ℝ => x t) (z.1 - rationalZakEta α p q * (k : ℝ)) *
        Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
          ((rationalZakEta α p q : ℂ) * (k : ℂ) * (z.2 : ℂ)))

/-- Algebraic finite-tail identity for the partial sums in
`Part7_student.tex`, Statement 1.  This isolates the purely finite-sum part of
the Cauchy estimate from the later finite Fourier Parseval step. -/
theorem rationalPositiveBaseFiberPartialSum_sub_eq_tail
    (α : ℝ) (p q M N : ℕ) (hMN : M ≤ N)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) :
    rationalPositiveBaseFiberPartialSum α p q N x z -
      rationalPositiveBaseFiberPartialSum α p q M x z =
      rationalPositiveBaseFiberPartialTail α p q M N x z := by
  unfold rationalPositiveBaseFiberPartialSum rationalPositiveBaseFiberPartialTail
  let sN : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let sM : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let f : ℤ → ℂ := fun k =>
    (fun t : ℝ => x t) (z.1 - rationalZakEta α p q * (k : ℝ)) *
      Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
        ((rationalZakEta α p q : ℂ) * (k : ℂ) * (z.2 : ℂ)))
  have hsub : sM ⊆ sN := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    constructor
    · exact le_trans (neg_le_neg (by exact_mod_cast hMN)) hk.1
    · exact le_trans hk.2 (by exact_mod_cast hMN)
  have hsum : ∑ k ∈ sN \ sM, f k =
      ∑ k ∈ sN, f k - ∑ k ∈ sM, f k := by
    have h := Finset.sum_sdiff (s₁ := sM) (s₂ := sN) (f := f) hsub
    rw [← h]
    abel
  simpa [sN, sM, f, sub_eq_add_neg] using hsum.symm

/-- Each shifted spatial sample occurring in the finite fiber partial sums is
an `L²` function on the rational-Zak spatial interval.  This is the one-variable
integrability input in the student's Statement 1 construction. -/
theorem rationalPositiveBaseFiberShiftedSample_memLp
    (α : ℝ) (p q : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) :
    MemLp
      (fun s : ℝ =>
        (fun t : ℝ => x t)
          (s - rationalZakEta α p q * (k : ℝ)))
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (fun t : ℝ => x t) (s - η * (k : ℝ)))
      ((volume : Measure ℝ).restrict S) := by
    exact ((Lp.stronglyMeasurable x).comp_measurable (by fun_prop)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have hΦ :
      Integrable
        (fun t : ℝ => ‖(fun u : ℝ => x u) t‖ ^ 2)
        (volume : Measure ℝ) :=
    Zak.integrable_norm_sq_of_memLp_two (Lp.memLp x)
  have hglobal :
      Integrable
        (fun s : ℝ =>
          ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2)
        (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using hΦ.comp_add_right (-η * (k : ℝ))
  simpa [η, S] using hglobal.mono_measure Measure.restrict_le_self

/-- The finite Fourier partial sums from `Part7_student.tex`, Statement 1, are
honest `L²` functions on `(0,η] × (0,η⁻¹]`.  The exponential phase has norm one,
so the result follows from the shifted-sample lemma, product lifting, and finite
closure of `MemLp` under sums. -/
theorem rationalPositiveBaseFiberPartialSum_memLp_product
    (α : ℝ) (p q N : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp
      (rationalPositiveBaseFiberPartialSum α p q N x)
      2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))) := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let T : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μS : Measure ℝ := (volume : Measure ℝ).restrict S
  let μT : Measure ℝ := (volume : Measure ℝ).restrict T
  unfold rationalPositiveBaseFiberPartialSum
  have hterm : ∀ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      MemLp
        (fun z : ℝ × ℝ =>
          (fun t : ℝ => x t) (z.1 - η * (k : ℝ)) *
            Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (z.2 : ℂ))))
        2 (μS.prod μT) := by
    intro k _hk
    have hsample :
        MemLp
          (fun s : ℝ => (fun t : ℝ => x t) (s - η * (k : ℝ)))
          2 μS := by
      simpa [η, S, μS] using
        rationalPositiveBaseFiberShiftedSample_memLp
          α p q x k
    have hbase :
        MemLp
          (fun z : ℝ × ℝ => (fun t : ℝ => x t) (z.1 - η * (k : ℝ)))
          2 (μS.prod μT) := by
      simpa using hsample.comp_fst μT
    have hmeas : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (fun t : ℝ => x t) (z.1 - η * (k : ℝ)) *
            Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (z.2 : ℂ))))
        (μS.prod μT) := by
      have hx : StronglyMeasurable
          (fun z : ℝ × ℝ =>
            (fun t : ℝ => x t) (z.1 - η * (k : ℝ))) := by
        exact (Lp.stronglyMeasurable x).comp_measurable (by fun_prop)
      have hphase : Continuous
          (fun z : ℝ × ℝ =>
            Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (z.2 : ℂ)))) := by
        fun_prop
      exact (hx.mul hphase.stronglyMeasurable).aestronglyMeasurable
    exact hbase.of_le hmeas (Filter.Eventually.of_forall fun z => by
      rw [norm_mul]
      have hphase :
          ‖Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (z.2 : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [hphase, mul_one])
  have hsum :=
    memLp_finsetSum
      (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
      (f := fun (k : ℤ) (z : ℝ × ℝ) =>
        (fun t : ℝ => x t) (z.1 - η * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((η : ℂ) * (k : ℂ) * (z.2 : ℂ))))
      hterm
  simpa [η, S, T, μS, μT] using hsum

/-- The finite partial sums from Statement 1, bundled as honest elements of
`L²((0,η] × (0,η⁻¹])`. -/
noncomputable def rationalPositiveBaseFiberPartialSum_Lp
    (α : ℝ) (p q : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) :
    Lp ℂ 2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))) :=
  (rationalPositiveBaseFiberPartialSum_memLp_product α p q N x).toLp
    (rationalPositiveBaseFiberPartialSum α p q N x)

/-- The finite Cauchy tail is an `L²` function on the product rectangle.  This
follows from the two finite partial sums and the algebraic tail identity. -/
theorem rationalPositiveBaseFiberPartialTail_memLp_product
    (α : ℝ) (p q M N : ℕ) (hMN : M ≤ N)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp
      (rationalPositiveBaseFiberPartialTail α p q M N x)
      2
      (((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))) := by
  let μQ : Measure (ℝ × ℝ) :=
    (((volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))
  have hdiff : MemLp
      (fun z : ℝ × ℝ =>
        rationalPositiveBaseFiberPartialSum α p q N x z -
          rationalPositiveBaseFiberPartialSum α p q M x z)
      2 μQ :=
    (rationalPositiveBaseFiberPartialSum_memLp_product α p q N x).sub
      (rationalPositiveBaseFiberPartialSum_memLp_product α p q M x)
  exact MemLp.ae_eq
    (Filter.Eventually.of_forall fun z =>
      rationalPositiveBaseFiberPartialSum_sub_eq_tail
        α p q M N hMN x z)
    hdiff

/-- The `Lp` difference of two finite partial sums is the `Lp` class of the
finite tail. -/
theorem rationalPositiveBaseFiberPartialSum_Lp_sub_eq_tail_toLp
    (α : ℝ) (p q M N : ℕ) (hMN : M ≤ N)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    rationalPositiveBaseFiberPartialSum_Lp α p q x N -
      rationalPositiveBaseFiberPartialSum_Lp α p q x M =
      (rationalPositiveBaseFiberPartialTail_memLp_product α p q M N hMN x).toLp
        (rationalPositiveBaseFiberPartialTail α p q M N x) := by
  let μQ : Measure (ℝ × ℝ) :=
    (((volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))
  let FN : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialSum α p q N x
  let FM : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialSum α p q M x
  let T : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialTail α p q M N x
  let hN : MemLp FN 2 μQ :=
    rationalPositiveBaseFiberPartialSum_memLp_product α p q N x
  let hM : MemLp FM 2 μQ :=
    rationalPositiveBaseFiberPartialSum_memLp_product α p q M x
  let hT : MemLp T 2 μQ :=
    rationalPositiveBaseFiberPartialTail_memLp_product α p q M N hMN x
  have hsub : hN.toLp FN - hM.toLp FM = (hN.sub hM).toLp (FN - FM) := by
    rw [← hN.toLp_sub hM]
  have htail_ae : (FN - FM) =ᵐ[μQ] T := by
    exact Filter.Eventually.of_forall fun z => by
      dsimp [FN, FM, T]
      exact rationalPositiveBaseFiberPartialSum_sub_eq_tail α p q M N hMN x z
  have htoLp_eq : (hN.sub hM).toLp (FN - FM) = hT.toLp T := by
    exact (hN.sub hM).toLp_congr hT htail_ae
  simpa [rationalPositiveBaseFiberPartialSum_Lp, μQ, FN, FM, T, hN, hM, hT] using
    hsub.trans htoLp_eq

/-- The distance between two finite partial sums is the real `L²` norm of the
finite tail. -/
theorem rationalPositiveBaseFiberPartialSum_Lp_dist_eq_lpNorm_tail
    (α : ℝ) (p q M N : ℕ) (hMN : M ≤ N)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    dist (rationalPositiveBaseFiberPartialSum_Lp α p q x N)
      (rationalPositiveBaseFiberPartialSum_Lp α p q x M) =
      lpNorm (rationalPositiveBaseFiberPartialTail α p q M N x) 2
        (((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
          ((volume : Measure ℝ).restrict
            (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))) := by
  let μQ : Measure (ℝ × ℝ) :=
    (((volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))
  let T : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialTail α p q M N x
  let hT : MemLp T 2 μQ :=
    rationalPositiveBaseFiberPartialTail_memLp_product α p q M N hMN x
  have hsub :=
    rationalPositiveBaseFiberPartialSum_Lp_sub_eq_tail_toLp α p q M N hMN x
  calc
    dist (rationalPositiveBaseFiberPartialSum_Lp α p q x N)
        (rationalPositiveBaseFiberPartialSum_Lp α p q x M)
        = ‖rationalPositiveBaseFiberPartialSum_Lp α p q x N -
            rationalPositiveBaseFiberPartialSum_Lp α p q x M‖ := by
          rw [dist_eq_norm]
    _ = ‖hT.toLp T‖ := by
          rw [hsub]
    _ = lpNorm T 2 μQ := by
          rw [Lp.norm_toLp]
          exact toReal_eLpNorm hT.aestronglyMeasurable
    _ = lpNorm (rationalPositiveBaseFiberPartialTail α p q M N x) 2
        (((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
          ((volume : Measure ℝ).restrict
            (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹))) := by
          simp [T, μQ]

/-- A single trigonometric monomial from the finite partial sums is an `L²`
function of the frequency variable on the fundamental interval. -/
theorem rationalPositiveBaseFiberPartialTerm_frequency_memLp
    (α : ℝ) (p q : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) (k : ℤ) :
    MemLp
      (fun ω : ℝ =>
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((rationalZakEta α p q : ℂ) * (k : ℂ) * (ω : ℂ))))
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
  let η : ℝ := rationalZakEta α p q
  let T : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μT : Measure ℝ := (volume : Measure ℝ).restrict T
  have hmeas : AEStronglyMeasurable
      (fun ω : ℝ =>
        (fun t : ℝ => x t) (s - η * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((η : ℂ) * (k : ℂ) * (ω : ℂ))))
      μT := by
    have hcont : Continuous
        (fun ω : ℝ =>
          (fun t : ℝ => x t) (s - η * (k : ℝ)) *
            Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (ω : ℂ)))) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  refine MemLp.of_bound hmeas
    (‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖) ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [norm_mul]
    have hphase :
        ‖Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((η : ℂ) * (k : ℂ) * (ω : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hphase, mul_one]

/-- For each fixed spatial point, the finite tail is an `L²` function of the
frequency variable.  This is the direct input needed to apply
`tsum_sq_fourierCoeffOn` in the next finite Parseval step. -/
theorem rationalPositiveBaseFiberPartialTail_frequency_memLp
    (α : ℝ) (p q M N : ℕ) (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) :
    MemLp
      (fun ω : ℝ => rationalPositiveBaseFiberPartialTail α p q M N x (s, ω))
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
  let η : ℝ := rationalZakEta α p q
  let T : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let μT : Measure ℝ := (volume : Measure ℝ).restrict T
  unfold rationalPositiveBaseFiberPartialTail
  have hterm : ∀ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
        Finset.Icc (-(M : ℤ)) (M : ℤ)),
      MemLp
        (fun ω : ℝ =>
          (fun t : ℝ => x t) (s - η * (k : ℝ)) *
            Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
              ((η : ℂ) * (k : ℂ) * (ω : ℂ))))
        2 μT := by
    intro k _hk
    simpa [η, T, μT] using
      rationalPositiveBaseFiberPartialTerm_frequency_memLp α p q x s k
  have hsum :=
    memLp_finsetSum
      (s := (Finset.Icc (-(N : ℤ)) (N : ℤ) \
        Finset.Icc (-(M : ℤ)) (M : ℤ)))
      (f := fun (k : ℤ) (ω : ℝ) =>
        (fun t : ℝ => x t) (s - η * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((η : ℂ) * (k : ℂ) * (ω : ℂ))))
      hterm
  simpa [η, T, μT] using hsum

/-- `fourierCoeffOn` is linear over finite sums of `L²` functions. -/
theorem rationalPositive_fourierCoeffOn_finset_sum
    {ι : Type*} [DecidableEq ι] {a b : ℝ} (hab : a < b)
    (u : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ u, MemLp (f i) 2 ((volume : Measure ℝ).restrict (Set.Ioc a b)))
    (j : ℤ) :
    fourierCoeffOn hab (fun ω : ℝ => ∑ i ∈ u, f i ω) j =
      ∑ i ∈ u, fourierCoeffOn hab (f i) j := by
  classical
  let T : ℝ := b - a
  have hT : 0 < T := sub_pos.mpr hab
  letI : Fact (0 < T) := ⟨hT⟩
  have hrewrite :
      AddCircle.liftIoc T a (fun x : ℝ => ∑ i ∈ u, f i x) =
        fun y : AddCircle T => ∑ i ∈ u, AddCircle.liftIoc T a (f i) y := by
    funext y
    simp [AddCircle.liftIoc]
  unfold fourierCoeffOn
  rw [hrewrite]
  have hfi : ∀ i ∈ u, Integrable (AddCircle.liftIoc T a (f i))
      (@AddCircle.haarAddCircle T ⟨hT⟩) := by
    intro i hi
    have hmem : MemLp (AddCircle.liftIoc T a (f i)) 2
        (@AddCircle.haarAddCircle T ⟨hT⟩) := by
      have hmemVol : MemLp (AddCircle.liftIoc T a (f i)) 2
          (volume : Measure (AddCircle T)) := by
        have hmemIoc : MemLp (f i) 2
            ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))) := by
          simpa [T, add_sub_cancel_left] using hf i hi
        exact hmemIoc.memLp_liftIoc
      exact hmemVol.haarAddCircle
    have h12 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
    exact hmem.integrable h12
  have hsum := fourierCoeff.sum
    (T := T) (s := u)
    (f := fun i : ι => AddCircle.liftIoc T a (f i)) hfi
  have hfunSum :
      (fun y : AddCircle T => ∑ i ∈ u, AddCircle.liftIoc T a (f i) y) =
        (∑ i ∈ u, AddCircle.liftIoc T a (f i)) := by
    funext y
    simp
  rw [hfunSum]
  simpa [T] using congrFun hsum j

/-- Linearity of `fourierCoeffOn` under subtraction for `L²` functions on an
interval.  This is the algebraic input for treating the coefficient extractor
as a bounded linear operator on product `L²`. -/
theorem rationalPositive_fourierCoeffOn_sub
    {a b : ℝ} (hab : a < b) {f g : ℝ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℝ).restrict (Set.Ioc a b)))
    (hg : MemLp g 2 ((volume : Measure ℝ).restrict (Set.Ioc a b)))
    (j : ℤ) :
    fourierCoeffOn hab (fun x : ℝ => f x - g x) j =
      fourierCoeffOn hab f j - fourierCoeffOn hab g j := by
  let T : ℝ := b - a
  have hT : 0 < T := sub_pos.mpr hab
  letI : Fact (0 < T) := ⟨hT⟩
  have hfLift : MemLp (AddCircle.liftIoc T a f) 2 AddCircle.haarAddCircle := by
    have hfIoc : MemLp f 2 ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))) := by
      simpa [T, add_sub_cancel_left] using hf
    exact hfIoc.memLp_liftIoc.haarAddCircle
  have hgLift : MemLp (AddCircle.liftIoc T a g) 2 AddCircle.haarAddCircle := by
    have hgIoc : MemLp g 2 ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))) := by
      simpa [T, add_sub_cancel_left] using hg
    exact hgIoc.memLp_liftIoc.haarAddCircle
  have h12 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
  have hfInt : Integrable (AddCircle.liftIoc T a f) AddCircle.haarAddCircle :=
    hfLift.integrable h12
  have hgInt : Integrable (AddCircle.liftIoc T a g) AddCircle.haarAddCircle :=
    hgLift.integrable h12
  have hsubfun :
      AddCircle.liftIoc T a (fun x : ℝ => f x - g x) =
        (fun y : AddCircle T => AddCircle.liftIoc T a f y -
          AddCircle.liftIoc T a g y) := by
    funext y
    simp [AddCircle.liftIoc]
  unfold fourierCoeffOn
  rw [hsubfun]
  have hlin :=
    fourierCoeff.add (T := T) (f := AddCircle.liftIoc T a f)
      (g := fun y : AddCircle T => - AddCircle.liftIoc T a g y)
      hfInt hgInt.neg
  have hneg :
      fourierCoeff (fun y : AddCircle T => - AddCircle.liftIoc T a g y) =
        - fourierCoeff (AddCircle.liftIoc T a g) := by
    funext n
    change fourierCoeff (-AddCircle.liftIoc T a g) n =
      -fourierCoeff (AddCircle.liftIoc T a g) n
    simpa using fourierCoeff.const_smul
      (T := T) (f := AddCircle.liftIoc T a g) (-1 : ℂ) n
  have hpoint := congrFun hlin j
  rw [hneg] at hpoint
  have haddfun :
      (AddCircle.liftIoc T a f + fun y : AddCircle T =>
        - AddCircle.liftIoc T a g y) =
      (fun y : AddCircle T =>
        AddCircle.liftIoc T a f y + -AddCircle.liftIoc T a g y) := by
    rfl
  have hpoint' :
      fourierCoeff
        (fun y : AddCircle T =>
          AddCircle.liftIoc T a f y + -AddCircle.liftIoc T a g y) j =
      fourierCoeff (AddCircle.liftIoc T a f) j +
        -fourierCoeff (AddCircle.liftIoc T a g) j := by
    rw [← haddfun]
    exact hpoint
  change fourierCoeff
      (fun y : AddCircle T => AddCircle.liftIoc T a f y -
        AddCircle.liftIoc T a g y) j =
      fourierCoeff (AddCircle.liftIoc T a f) j -
        fourierCoeff (AddCircle.liftIoc T a g) j
  simpa [sub_eq_add_neg] using hpoint'

/-- Completeness of the AddCircle Fourier basis: two `L²` circle functions
with the same Fourier coefficients are equal. -/
theorem addCircle_L2_ext_of_fourierCoeff_eq
    {T : ℝ} [Fact (0 < T)]
    (F G : Lp ℂ 2 AddCircle.haarAddCircle)
    (h : ∀ k : ℤ, fourierCoeff (fun x : AddCircle T => F x) k =
      fourierCoeff (fun x : AddCircle T => G x) k) :
    F = G := by
  apply (LinearIsometryEquiv.injective (fourierBasis (T := T)).repr)
  ext k
  rw [fourierBasis_repr, fourierBasis_repr]
  exact h k

/-- Lifted interval functions are a.e. equal on the AddCircle once their lifted
Fourier coefficients agree. This is the uniqueness tool needed for identifying
Riesz-Fischer limits with the guarded frequency fiber. -/
theorem liftIoc_ae_eq_of_fourierCoeff_eq
    {T a : ℝ} [Fact (0 < T)] {f g : ℝ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))))
    (hg : MemLp g 2 ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))))
    (hcoeff : ∀ k : ℤ,
      fourierCoeff (AddCircle.liftIoc T a f) k =
      fourierCoeff (AddCircle.liftIoc T a g) k) :
    AddCircle.liftIoc T a f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc T a g := by
  let Ffun : AddCircle T → ℂ := AddCircle.liftIoc T a f
  let Gfun : AddCircle T → ℂ := AddCircle.liftIoc T a g
  have hfLift : MemLp Ffun 2 AddCircle.haarAddCircle := by
    simpa [Ffun] using hf.memLp_liftIoc.haarAddCircle
  have hgLift : MemLp Gfun 2 AddCircle.haarAddCircle := by
    simpa [Gfun] using hg.memLp_liftIoc.haarAddCircle
  let F : Lp ℂ 2 AddCircle.haarAddCircle := hfLift.toLp Ffun
  let G : Lp ℂ 2 AddCircle.haarAddCircle := hgLift.toLp Gfun
  have hFG : F = G := by
    apply addCircle_L2_ext_of_fourierCoeff_eq
    intro k
    have hFcoeff : fourierCoeff (fun x : AddCircle T => F x) k =
        fourierCoeff Ffun k := by
      simpa [F] using congrFun (fourierCoeff_congr_ae hfLift.coeFn_toLp) k
    have hGcoeff : fourierCoeff (fun x : AddCircle T => G x) k =
        fourierCoeff Gfun k := by
      simpa [G] using congrFun (fourierCoeff_congr_ae hgLift.coeFn_toLp) k
    calc
      fourierCoeff (fun x : AddCircle T => F x) k = fourierCoeff Ffun k := hFcoeff
      _ = fourierCoeff Gfun k := by simpa [Ffun, Gfun] using hcoeff k
      _ = fourierCoeff (fun x : AddCircle T => G x) k := hGcoeff.symm
  have hAe : (fun x : AddCircle T => F x) =ᵐ[AddCircle.haarAddCircle]
      fun x : AddCircle T => G x := by
    exact Lp.ext_iff.mp hFG
  have hFae : (fun x : AddCircle T => F x) =ᵐ[AddCircle.haarAddCircle] Ffun := by
    simpa [F] using hfLift.coeFn_toLp
  have hGae : (fun x : AddCircle T => G x) =ᵐ[AddCircle.haarAddCircle] Gfun := by
    simpa [G] using hgLift.coeFn_toLp
  exact hFae.symm.trans (hAe.trans hGae)

/-- Single interval Fourier coefficients are bounded by the `L²` norm on the
interval.  This is the one-dimensional continuity estimate for the student's
coefficient operator `C_j`. -/
theorem fourierCoeffOn_norm_sq_le_intervalIntegral
    {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℝ).restrict (Set.Ioc a b))) (j : ℤ) :
    ‖fourierCoeffOn hab f j‖ ^ 2 ≤
      (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2 := by
  have hsumm : Summable fun i : ℤ => ‖fourierCoeffOn hab f i‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn hab hf).summable
  have hsingle :
      (∑ i ∈ ({j} : Finset ℤ), ‖fourierCoeffOn hab f i‖ ^ 2) ≤
        ∑' i : ℤ, ‖fourierCoeffOn hab f i‖ ^ 2 := by
    exact hsumm.sum_le_tsum ({j} : Finset ℤ)
      (fun i _hi => sq_nonneg _)
  have hparse := tsum_sq_fourierCoeffOn (a := a) (b := b) (f := f) hab hf
  simpa [hparse] using hsingle

/-- Rational-`η` specialization of the interval coefficient bound, in the
normalization used in `Part7_student.tex`: `|C_j F|² ≤ η ∫ |F|²`. -/
theorem rationalPositive_fourierCoeffOn_norm_sq_le_eta_setIntegral
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {F : ℝ → ℂ}
    (hF : MemLp F 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)))
    (j : ℤ) :
    ‖fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      F j‖ ^ 2 ≤
      rationalZakEta α p q *
        (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖F ω‖ ^ 2) := by
  let η : ℝ := rationalZakEta α p q
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  let hab : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  have hbound :=
    fourierCoeffOn_norm_sq_le_intervalIntegral
      (a := (0 : ℝ)) (b := η⁻¹) hab (f := F) (by simpa [η] using hF) j
  calc
    ‖fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      F j‖ ^ 2
        ≤ (η⁻¹ - (0 : ℝ))⁻¹ • ∫ ω in (0 : ℝ)..η⁻¹, ‖F ω‖ ^ 2 := by
          simpa [η, hab] using hbound
    _ = η * (∫ ω in Set.Ioc (0 : ℝ) η⁻¹, ‖F ω‖ ^ 2) := by
          rw [sub_zero, inv_inv]
          rw [intervalIntegral.integral_of_le hab.le]
          simp
    _ = rationalZakEta α p q *
        (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖F ω‖ ^ 2) := by
          simp [η]

/-- Fourier coefficient of a single trigonometric monomial appearing in the
finite partial sums.  This is the atomic orthogonality calculation used in the
finite-tail Parseval estimate from `Part7_student.tex`, Statement 1. -/
theorem rationalPositiveBaseFiberPartialTerm_fourierCoeffOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (k j : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ =>
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((rationalZakEta α p q : ℂ) * (k : ℂ) * (ω : ℂ)))) j =
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
        (Pi.single k (1 : ℂ) : ℤ → ℂ) j := by
  let η : ℝ := rationalZakEta α p q
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  letI : Fact (0 < (rationalZakEta α p q)⁻¹) :=
    ⟨inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ)⟩
  let c : ℂ := (fun t : ℝ => x t)
    (s - rationalZakEta α p q * (k : ℝ))
  have hfun :
      (fun ω : ℝ =>
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((rationalZakEta α p q : ℂ) * (k : ℂ) * (ω : ℂ)))) =
        fun ω : ℝ => c * fourier k
          (ω : AddCircle (rationalZakEta α p q)⁻¹) := by
    funext ω
    rw [fourier_coe_apply]
    have hη_ne : η ≠ 0 := ne_of_gt hη
    have hηc_ne : (η : ℂ) ≠ 0 := by exact_mod_cast hη_ne
    have harg :
        (2 * (Real.pi : ℂ)) * Complex.I *
            ((η : ℂ) * (k : ℂ) * (ω : ℂ)) =
          2 * ↑Real.pi * Complex.I * ↑k * ↑ω / ↑(η⁻¹) := by
      field_simp [hηc_ne]
      have hdiv : ((1 / η : ℝ) : ℂ) = (η : ℂ)⁻¹ := by
        rw [Complex.ofReal_div]
        simp
      rw [hdiv]
      field_simp [hηc_ne]
    simp [c, η, harg]
  rw [hfun]
  rw [fourierCoeffOn.const_mul]
  rw [Zak.fourierCoeffOn_coeAddCircle_eq_fourierCoeff]
  rw [fourierCoeff_fourier]

/-- Fourier coefficient of the finite Cauchy tail from
`Part7_student.tex`, Statement 1.  This is the finite-sum version of the
coefficient identity used before applying Parseval to the tail. -/
theorem rationalPositiveBaseFiberPartialTail_fourierCoeffOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (M N : ℕ) (j : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ => rationalPositiveBaseFiberPartialTail α p q M N x (s, ω)) j =
      ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
          (Pi.single k (1 : ℂ) : ℤ → ℂ) j := by
  classical
  let u : Finset ℤ :=
    Finset.Icc (-(N : ℤ)) (N : ℤ) \
      Finset.Icc (-(M : ℤ)) (M : ℤ)
  let hab : (0 : ℝ) < (rationalZakEta α p q)⁻¹ :=
    inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ)
  let f : ℤ → ℝ → ℂ := fun k ω =>
    (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
      Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
        ((rationalZakEta α p q : ℂ) * (k : ℂ) * (ω : ℂ)))
  have hf : ∀ k ∈ u,
      MemLp (f k) 2
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
    intro k _hk
    simpa [f] using
      rationalPositiveBaseFiberPartialTerm_frequency_memLp α p q x s k
  have hsum :=
    rationalPositive_fourierCoeffOn_finset_sum
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      hab u f hf j
  unfold rationalPositiveBaseFiberPartialTail
  change fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹) hab
      (fun ω : ℝ => ∑ k ∈ u, f k ω) j =
    ∑ k ∈ u,
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
        (Pi.single k (1 : ℂ) : ℤ → ℂ) j
  rw [hsum]
  exact Finset.sum_congr rfl fun k _hk =>
    rationalPositiveBaseFiberPartialTerm_fourierCoeffOn
      hα hβ hgap hαβ s x k j

/-- Fourier coefficient of a finite partial sum from
`Part7_student.tex`, Statement 1.  This is the finite form of the student's
coefficient operator identity `C_j F_N = x(· - η j)`. -/
theorem rationalPositiveBaseFiberPartialSum_fourierCoeffOn
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
          (Pi.single k (1 : ℂ) : ℤ → ℂ) j := by
  classical
  let u : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let hab : (0 : ℝ) < (rationalZakEta α p q)⁻¹ :=
    inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ)
  let f : ℤ → ℝ → ℂ := fun k ω =>
    (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
      Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
        ((rationalZakEta α p q : ℂ) * (k : ℂ) * (ω : ℂ)))
  have hf : ∀ k ∈ u,
      MemLp (f k) 2
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹)) := by
    intro k _hk
    simpa [f] using
      rationalPositiveBaseFiberPartialTerm_frequency_memLp α p q x s k
  have hsum :=
    rationalPositive_fourierCoeffOn_finset_sum
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      hab u f hf j
  unfold rationalPositiveBaseFiberPartialSum
  change fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹) hab
      (fun ω : ℝ => ∑ k ∈ u, f k ω) j =
    ∑ k ∈ u,
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ)) *
        (Pi.single k (1 : ℂ) : ℤ → ℂ) j
  rw [hsum]
  exact Finset.sum_congr rfl fun k _hk =>
    rationalPositiveBaseFiberPartialTerm_fourierCoeffOn
      hα hβ hgap hαβ s x k j

/-- Evaluating a finite sum of scalar multiples of coordinate functions gives
the corresponding coefficient on the support and zero off the support. -/
theorem rationalPositive_finset_sum_mul_pi_single_apply
    (u : Finset ℤ) (c : ℤ → ℂ) (j : ℤ) :
    (∑ k ∈ u, c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) j) =
      if j ∈ u then c j else 0 := by
  classical
  by_cases hj : j ∈ u
  · rw [if_pos hj]
    calc
      (∑ k ∈ u, c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) j) =
          c j * (Pi.single j (1 : ℂ) : ℤ → ℂ) j := by
            refine Finset.sum_eq_single j ?_ ?_
            · intro k hk hkj
              rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]
            · intro hjnot
              exact False.elim (hjnot hj)
      _ = c j := by simp
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun k hk => by
      have hkj : k ≠ j := by
        intro h
        subst h
        exact hj hk
      rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]

/-- Stabilized Fourier coefficient of the finite partial sum: if the index
`j` lies in the truncation window, then the coefficient is the spatial sample
`x(s - η j)`. -/
theorem rationalPositiveBaseFiberPartialSum_fourierCoeffOn_of_mem
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ)
    (hj : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j =
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)) := by
  rw [rationalPositiveBaseFiberPartialSum_fourierCoeffOn
    hα hβ hgap hαβ s x N j]
  rw [rationalPositive_finset_sum_mul_pi_single_apply]
  simp [hj]

/-- Stabilized Fourier coefficient in the student's `N ≥ |j|` form. -/
theorem rationalPositiveBaseFiberPartialSum_fourierCoeffOn_of_natAbs_le
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ)
    (hj : j.natAbs ≤ N) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
      (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
        inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
      (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j =
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)) :=
  rationalPositiveBaseFiberPartialSum_fourierCoeffOn_of_mem
    hα hβ hgap hαβ s x N j
    (int_mem_symmetric_Icc_of_natAbs_le hj)

/-- Spatial-function form of the stabilized coefficient identity.  For every
`N ≥ |j|`, the `j`-th frequency coefficient of the finite partial sum is the
shifted sample function `s ↦ x(s - ηj)`. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_eq_sample_of_natAbs_le
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ)
    (hj : j.natAbs ≤ N) :
    (fun s : ℝ =>
      fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j) =
      fun s : ℝ =>
        (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)) := by
  funext s
  exact rationalPositiveBaseFiberPartialSum_fourierCoeffOn_of_natAbs_le
    hα hβ hgap hαβ s x N j hj

/-- Once the truncation contains `j`, the coefficient section `s ↦ C_j F_N(s)`
is an `L²` function of the spatial variable because it is exactly the shifted
sample `s ↦ x(s - ηj)`. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_memLp_of_natAbs_le
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ)
    (hj : j.natAbs ≤ N) :
    MemLp
      (fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
          (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j)
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) := by
  rw [rationalPositiveBaseFiberPartialSum_coeffSection_eq_sample_of_natAbs_le
    hα hβ hgap hαβ x N j hj]
  exact rationalPositiveBaseFiberShiftedSample_memLp α p q x j

/-- The `j`-th coefficient section of every finite base partial sum is an
honest `L²(0, eta]` function.  Before the truncation reaches `j` it is the zero
section; afterwards it is the shifted spatial sample. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_memLp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ) :
    MemLp
      (fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
          (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j)
      2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) := by
  by_cases hj : j.natAbs ≤ N
  · exact rationalPositiveBaseFiberPartialSum_coeffSection_memLp_of_natAbs_le
      hα hβ hgap hαβ x N j hj
  · have hnotmem : j ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      intro hjmem
      rw [Finset.mem_Icc] at hjmem
      have hnat : j.natAbs ≤ N := by
        rcases Int.natAbs_eq j with hcases | hcases
        · rw [hcases]
          omega
        · rw [hcases]
          omega
      exact hj hnat
    have hzero :
        (fun s : ℝ =>
          fourierCoeffOn
            (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
            (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
              inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
            (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j) =
          fun _ : ℝ => (0 : ℂ) := by
      funext s
      rw [rationalPositiveBaseFiberPartialSum_fourierCoeffOn
        hα hβ hgap hαβ s x N j]
      rw [rationalPositive_finset_sum_mul_pi_single_apply]
      simp [hnotmem]
    rw [hzero]
    exact MemLp.zero

/-- The finite base partial-sum coefficient section as an element of
`L²(0, eta]`. -/
noncomputable def rationalPositiveBaseFiberPartialSum_coeffSection_Lp
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (N : ℕ) (j : ℤ) :
    Lp ℂ 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) :=
  (rationalPositiveBaseFiberPartialSum_coeffSection_memLp
    hα hβ hgap hαβ x N j).toLp
    (fun s : ℝ =>
      fourierCoeffOn
        (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
        (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
          inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
        (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j)

/-- The shifted spatial sample appearing as the stabilized finite coefficient
section, bundled as an `L²(0, eta]` class. -/
noncomputable def rationalPositiveBaseFiberShiftedSample_Lp
    (α : ℝ) (p q : ℕ)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (j : ℤ) :
    Lp ℂ 2
      ((volume : Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))) :=
  (rationalPositiveBaseFiberShiftedSample_memLp α p q x j).toLp
    (fun s : ℝ =>
      (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)))

/-- As `L²(0, eta]` classes, the finite coefficient sections are eventually
equal to the shifted sample.  This packages the student's finite
eventual-stabilization in the exact topology used by the product-limit
argument. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_Lp_eventually_eq_sample
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (j : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      rationalPositiveBaseFiberPartialSum_coeffSection_Lp
        hα hβ hgap hαβ x N j =
      rationalPositiveBaseFiberShiftedSample_Lp α p q x j := by
  refine Filter.eventually_atTop.2 ⟨j.natAbs, ?_⟩
  intro N hN
  unfold rationalPositiveBaseFiberPartialSum_coeffSection_Lp
    rationalPositiveBaseFiberShiftedSample_Lp
  have hfun :=
    rationalPositiveBaseFiberPartialSum_coeffSection_eq_sample_of_natAbs_le
      hα hβ hgap hαβ x N j hN
  have hae :
      (fun s : ℝ =>
        fourierCoeffOn
          (a := (0 : ℝ)) (b := (rationalZakEta α p q)⁻¹)
          (show (0 : ℝ) < (rationalZakEta α p q)⁻¹ from
            inv_pos.mpr (rationalZakEta_pos hα hβ hgap hαβ))
          (fun ω : ℝ => rationalPositiveBaseFiberPartialSum α p q N x (s, ω)) j)
        =ᵐ[((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (rationalZakEta α p q)))]
        fun s : ℝ =>
          (fun t : ℝ => x t) (s - rationalZakEta α p q * (j : ℝ)) :=
    Filter.Eventually.of_forall fun s => congrFun hfun s
  exact
    (rationalPositiveBaseFiberPartialSum_coeffSection_memLp
      hα hβ hgap hαβ x N j).toLp_congr
      (rationalPositiveBaseFiberShiftedSample_memLp α p q x j) hae

/-- The finite coefficient-section `L²(0, eta]` classes converge to the
shifted sample class.  This is the topology-facing form of eventual
stabilization. -/
theorem rationalPositiveBaseFiberPartialSum_coeffSection_Lp_tendsto_sample
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (j : ℤ) :
    Filter.Tendsto
      (fun N : ℕ =>
        rationalPositiveBaseFiberPartialSum_coeffSection_Lp
          hα hβ hgap hαβ x N j)
      Filter.atTop
      (nhds (rationalPositiveBaseFiberShiftedSample_Lp α p q x j)) :=
  tendsto_nhds_of_eventually_eq
    (rationalPositiveBaseFiberPartialSum_coeffSection_Lp_eventually_eq_sample
      hα hβ hgap hαβ x j)

/-- The squared `ℓ²` norm of a finite coordinate-supported sequence is the
finite sum of squared coefficient norms. -/
theorem rationalPositive_tsum_norm_sq_finset_pi_single
    (u : Finset ℤ) (c : ℤ → ℂ) :
    (∑' j : ℤ,
        ‖∑ k ∈ u, c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) j‖ ^ 2) =
      ∑ k ∈ u, ‖c k‖ ^ 2 := by
  classical
  have hzero : ∀ j ∉ u,
      ‖∑ k ∈ u, c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) j‖ ^ 2 = 0 := by
    intro j hj
    rw [rationalPositive_finset_sum_mul_pi_single_apply, if_neg hj, norm_zero]
    norm_num
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [rationalPositive_finset_sum_mul_pi_single_apply, if_pos hj]

/-- Finite Parseval identity for the named Cauchy tail in
`Part7_student.tex`, Statement 1. -/
theorem rationalPositiveBaseFiberPartialTail_parseval
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (s : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) (M N : ℕ) :
    rationalZakEta α p q *
        (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFiberPartialTail α p q M N x (s, ω)‖ ^ 2) =
      ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  classical
  let η : ℝ := rationalZakEta α p q
  have hη : 0 < η := rationalZakEta_pos hα hβ hgap hαβ
  let hab : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  let F : ℝ → ℂ := fun ω : ℝ =>
    rationalPositiveBaseFiberPartialTail α p q M N x (s, ω)
  have hmem : MemLp F 2 ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) η⁻¹)) := by
    simpa [F, η] using
      rationalPositiveBaseFiberPartialTail_frequency_memLp α p q M N x s
  have hparseval :=
    tsum_sq_fourierCoeffOn
      (a := (0 : ℝ)) (b := η⁻¹) (f := F) hab hmem
  let u : Finset ℤ :=
    Finset.Icc (-(N : ℤ)) (N : ℤ) \
      Finset.Icc (-(M : ℤ)) (M : ℤ)
  let c : ℤ → ℂ := fun k =>
    (fun t : ℝ => x t) (s - η * (k : ℝ))
  calc
    rationalZakEta α p q *
        (∫ ω in Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹, ‖F ω‖ ^ 2)
        = (η⁻¹ - (0 : ℝ))⁻¹ •
            (∫ ω in (0 : ℝ)..η⁻¹, ‖F ω‖ ^ 2) := by
          rw [sub_zero, inv_inv]
          rw [intervalIntegral.integral_of_le hab.le]
          simp [η]
    _ = ∑' j : ℤ, ‖fourierCoeffOn (a := (0 : ℝ)) (b := η⁻¹) hab F j‖ ^ 2 := by
          rw [hparseval]
    _ = ∑' j : ℤ, ‖∑ k ∈ u,
            c k * (Pi.single k (1 : ℂ) : ℤ → ℂ) j‖ ^ 2 := by
          apply tsum_congr
          intro j
          rw [rationalPositiveBaseFiberPartialTail_fourierCoeffOn
            hα hβ hgap hαβ s x M N j]
    _ = ∑ k ∈ u, ‖c k‖ ^ 2 :=
          rationalPositive_tsum_norm_sq_finset_pi_single u c
    _ = ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
          simp [u, c, η]

/-- Product-integral form of the finite Cauchy-tail Parseval identity. -/
theorem rationalPositiveBaseFiberPartialTail_product_parseval
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (M N : ℕ) (hMN : M ≤ N) :
    rationalZakEta α p q *
        (∫ z in Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
            Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
            Finset.Icc (-(M : ℤ)) (M : ℤ)),
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let U : Set ℝ := Set.Ioc (0 : ℝ) η⁻¹
  let Tail : ℝ × ℝ → ℂ := rationalPositiveBaseFiberPartialTail α p q M N x
  let H : ℝ × ℝ → ℝ := fun z => ‖Tail z‖ ^ 2
  have htail_mem :=
    rationalPositiveBaseFiberPartialTail_memLp_product α p q M N hMN x
  have htail_int_measure :
      Integrable H
        (((volume : Measure ℝ).restrict S).prod
          ((volume : Measure ℝ).restrict U)) := by
    rw [← MeasureTheory.memLp_two_iff_integrable_sq_norm
      htail_mem.aestronglyMeasurable]
    simpa [H, Tail, S, U, η] using htail_mem
  have htail_int_on :
      IntegrableOn H (S ×ˢ U)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [IntegrableOn, H, Tail, S, U, Measure.prod_restrict] using
      htail_int_measure
  have hfubini :
      (∫ z in S ×ˢ U, H z ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
        ∫ s in S, ∫ ω in U, H (s, ω) ∂(volume : Measure ℝ)
          ∂(volume : Measure ℝ) := by
    exact setIntegral_prod
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := H) (s := S) (t := U) htail_int_on
  calc
    rationalZakEta α p q *
        (∫ z in Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
            Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
        η * (∫ z in S ×ˢ U, H z
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
          simp [η, S, U, H, Tail]
    _ = η * (∫ s in S, ∫ ω in U, H (s, ω) ∂(volume : Measure ℝ)
          ∂(volume : Measure ℝ)) := by
          rw [hfubini]
    _ = ∫ s in S,
          η * (∫ ω in U, H (s, ω) ∂(volume : Measure ℝ))
          ∂(volume : Measure ℝ) := by
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ s in S,
        ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
            Finset.Icc (-(M : ℤ)) (M : ℤ)),
          ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Ioc ?_
          intro s _hs
          simpa [H, Tail, U, η] using
            rationalPositiveBaseFiberPartialTail_parseval
              hα hβ hgap hαβ s x M N
    _ = ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
            Finset.Icc (-(M : ℤ)) (M : ℤ)),
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
          simp [S, η]

/-- Product tail Parseval with the spatial integral pushed through the finite
tail sum.  The right-hand side is now a finite tail of the summable spatial
periodization series. -/
theorem rationalPositiveBaseFiberPartialTail_product_parseval_sum_integral
    {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (M N : ℕ) (hMN : M ≤ N) :
    rationalZakEta α p q *
        (∫ z in Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
            Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
  classical
  let η : ℝ := rationalZakEta α p q
  let S : Set ℝ := Set.Ioc (0 : ℝ) η
  let u : Finset ℤ :=
    Finset.Icc (-(N : ℤ)) (N : ℤ) \
      Finset.Icc (-(M : ℤ)) (M : ℤ)
  let f : ℤ → ℝ → ℝ := fun k s =>
    ‖(fun t : ℝ => x t) (s - η * (k : ℝ))‖ ^ 2
  have hterm : ∀ k ∈ u, Integrable (f k) ((volume : Measure ℝ).restrict S) := by
    intro k _hk
    have hmem :=
      rationalPositiveBaseFiberShiftedSample_memLp α p q x k
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm
      hmem.aestronglyMeasurable] at hmem
    simpa [f, S, η] using hmem
  calc
    rationalZakEta α p q *
        (∫ z in Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ
            Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹,
          ‖rationalPositiveBaseFiberPartialTail α p q M N x z‖ ^ 2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      ∫ s in S, ∑ k ∈ u, f k s := by
        simpa [S, u, f, η] using
          rationalPositiveBaseFiberPartialTail_product_parseval
            hα hβ hgap hαβ x M N hMN
    _ = ∑ k ∈ u, ∫ s in S, f k s := by
        rw [MeasureTheory.integral_finsetSum]
        exact hterm
    _ = ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) \
          Finset.Icc (-(M : ℤ)) (M : ℤ)),
        ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ‖(fun t : ℝ => x t) (s - rationalZakEta α p q * (k : ℝ))‖ ^ 2 := by
        simp [u, f, S, η]
end LyubarskiiNes.RationalDensity
