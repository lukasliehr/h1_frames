import LeanCode.ZakTransform.ZakDef

open scoped BigOperators
open MeasureTheory

namespace Zak

/-- Riesz-Fischer construction for circle Fourier series: a square-summable
coefficient sequence determines an `L²` function on the additive circle. -/
noncomputable def circleFourierL2OfCoeffs
    {T : ℝ}
    [hT : Fact (0 < T)]
    (c : ℤ → ℂ)
    (hc : Summable fun k : ℤ => ‖c k‖ ^ 2) :
    Lp ℂ 2 (@AddCircle.haarAddCircle T hT) :=
  (@fourierBasis T hT).repr.symm
    (⟨c, by
      apply memℓp_gen
      simpa using hc⟩ : lp (fun _ : ℤ => ℂ) 2)

/-- The Riesz-Fischer circle fiber has the prescribed Fourier coefficients. -/
theorem fourierCoeff_circleFourierL2OfCoeffs
    {T : ℝ}
    [hT : Fact (0 < T)]
    (c : ℤ → ℂ)
    (hc : Summable fun k : ℤ => ‖c k‖ ^ 2)
    (k : ℤ) :
    fourierCoeff (circleFourierL2OfCoeffs (T := T) c hc) k = c k := by
  rw [← fourierBasis_repr]
  simp [circleFourierL2OfCoeffs]

/-- The interval representative of the Riesz-Fischer circle fiber is an `L²`
function on every fundamental interval. -/
theorem circleFourierL2OfCoeffs_memLp_interval
    {T : ℝ}
    [hT : Fact (0 < T)]
    (a : ℝ)
    (c : ℤ → ℂ)
    (hc : Summable fun k : ℤ => ‖c k‖ ^ 2) :
    MemLp
      (fun ω : ℝ =>
        circleFourierL2OfCoeffs (T := T) c hc (ω : AddCircle T))
      2
      ((volume : Measure ℝ).restrict (Set.Ioc a (a + T))) := by
  let F : Lp ℂ 2 (@AddCircle.haarAddCircle T hT) :=
    circleFourierL2OfCoeffs (T := T) c hc
  have hLpHaar :
      MemLp (fun z : AddCircle T => F z) 2
        (@AddCircle.haarAddCircle T hT) := by
    exact Lp.memLp F
  have hLpVol :
      MemLp (fun z : AddCircle T => F z) 2
        (volume : Measure (AddCircle T)) := by
    exact hLpHaar.of_haarAddCircle
  have hcomp :=
    hLpVol.comp_measurePreserving (AddCircle.measurePreserving_mk T a)
  simpa [F, Function.comp_def] using hcomp

/-- The interval Fourier coefficient of a real representative of a circle
function is the corresponding Fourier coefficient on the additive circle. -/
theorem fourierCoeffOn_coeAddCircle_eq_fourierCoeff
    {T : ℝ}
    [hT : Fact (0 < T)]
    (F : AddCircle T → ℂ)
    (k : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := T)
      (show (0 : ℝ) < T from hT.out)
      (fun ω : ℝ => F (ω : AddCircle T)) k =
        fourierCoeff F k := by
  rw [fourierCoeffOn_eq_integral]
  rw [fourierCoeff_eq_intervalIntegral F k (0 : ℝ)]
  simp

/-- The interval Fourier coefficients of the Riesz-Fischer interval
representative are the original square-summable coefficients. -/
theorem fourierCoeffOn_circleFourierL2OfCoeffs
    {T : ℝ}
    [hT : Fact (0 < T)]
    (c : ℤ → ℂ)
    (hc : Summable fun k : ℤ => ‖c k‖ ^ 2)
    (k : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := T)
      (show (0 : ℝ) < T from hT.out)
      (fun ω : ℝ =>
        circleFourierL2OfCoeffs (T := T) c hc (ω : AddCircle T)) k =
        c k := by
  rw [fourierCoeffOn_coeAddCircle_eq_fourierCoeff]
  exact fourierCoeff_circleFourierL2OfCoeffs c hc k

/-- The honest `L²` frequency fiber determined by Zak sample coefficients at a
spatial point `x`.  This avoids asserting pointwise convergence of the raw
`tsum` defining `zakTransform`; the fiber is constructed by Riesz-Fischer from
the square-summable coefficient sequence. -/
noncomputable def zakL2FrequencyFiber
    (ρ : ℝ)
    (hρ : 0 < ρ)
    (f : ℝ → ℂ)
    (x : ℝ)
    (hc : Summable fun k : ℤ => ‖f (x - ρ * (k : ℝ))‖ ^ 2) :
    Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) ρ⁻¹)) := by
  letI : Fact (0 < ρ⁻¹) := ⟨inv_pos.mpr hρ⟩
  let c : ℤ → ℂ := fun k => f (x - ρ * (k : ℝ))
  let F : ℝ → ℂ := fun ω : ℝ =>
    circleFourierL2OfCoeffs (T := ρ⁻¹) c hc (ω : AddCircle ρ⁻¹)
  exact MemLp.toLp F
    (by
      simpa [F, c, zero_add] using
        circleFourierL2OfCoeffs_memLp_interval
          (T := ρ⁻¹) (a := (0 : ℝ)) c hc)

/-- The `L²` Zak frequency fiber has interval Fourier coefficients equal to the
original spatial samples. -/
theorem zakL2FrequencyFiber_fourierCoeffOn
    (ρ : ℝ)
    (hρ : 0 < ρ)
    (f : ℝ → ℂ)
    (x : ℝ)
    (hc : Summable fun k : ℤ => ‖f (x - ρ * (k : ℝ))‖ ^ 2)
    (k : ℤ) :
    fourierCoeffOn
      (a := (0 : ℝ)) (b := ρ⁻¹)
      (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
      (fun ω : ℝ => zakL2FrequencyFiber ρ hρ f x hc ω) k =
        f (x - ρ * (k : ℝ)) := by
  letI : Fact (0 < ρ⁻¹) := ⟨inv_pos.mpr hρ⟩
  let c : ℤ → ℂ := fun k => f (x - ρ * (k : ℝ))
  let F : ℝ → ℂ := fun ω : ℝ =>
    circleFourierL2OfCoeffs (T := ρ⁻¹) c hc (ω : AddCircle ρ⁻¹)
  let hF : MemLp F 2 ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) ρ⁻¹)) := by
    simpa [F, c, zero_add] using
      circleFourierL2OfCoeffs_memLp_interval
        (T := ρ⁻¹) (a := (0 : ℝ)) c hc
  have hcongr :
      fourierCoeffOn
        (a := (0 : ℝ)) (b := ρ⁻¹)
        (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
        (fun ω : ℝ => hF.toLp F ω) =
      fourierCoeffOn
        (a := (0 : ℝ)) (b := ρ⁻¹)
        (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
        F := by
    exact fourierCoeffOn_congr_ae
      (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
      hF.coeFn_toLp
  calc
    fourierCoeffOn
      (a := (0 : ℝ)) (b := ρ⁻¹)
      (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
      (fun ω : ℝ => zakL2FrequencyFiber ρ hρ f x hc ω) k
        = fourierCoeffOn
            (a := (0 : ℝ)) (b := ρ⁻¹)
            (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
            (fun ω : ℝ => hF.toLp F ω) k := by
              simp [zakL2FrequencyFiber, F, c]
    _ = fourierCoeffOn
            (a := (0 : ℝ)) (b := ρ⁻¹)
            (show (0 : ℝ) < ρ⁻¹ from inv_pos.mpr hρ)
            F k := by
              exact congrFun hcongr k
    _ = f (x - ρ * (k : ℝ)) := by
      simpa [F, c] using
        fourierCoeffOn_circleFourierL2OfCoeffs (T := ρ⁻¹) c hc k

/-- Parseval's identity for the true `L²` Zak frequency fiber at a fixed
spatial point. -/
theorem zakL2FrequencyFiber_parseval
    (ρ : ℝ)
    (hρ : 0 < ρ)
    (f : ℝ → ℂ)
    (x : ℝ)
    (hc : Summable fun k : ℤ => ‖f (x - ρ * (k : ℝ))‖ ^ 2) :
    ρ * (∫ ω in Set.Ioc (0 : ℝ) ρ⁻¹,
      ‖zakL2FrequencyFiber ρ hρ f x hc ω‖ ^ 2) =
      ∑' k : ℤ, ‖f (x - ρ * (k : ℝ))‖ ^ 2 := by
  let hab : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ
  let F : ℝ → ℂ := fun ω : ℝ => zakL2FrequencyFiber ρ hρ f x hc ω
  have hmem : MemLp F 2 ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) ρ⁻¹)) := by
    exact Lp.memLp (zakL2FrequencyFiber ρ hρ f x hc)
  have hparseval :=
    tsum_sq_fourierCoeffOn
      (a := (0 : ℝ)) (b := ρ⁻¹)
      (f := F) hab hmem
  symm
  calc
    (∑' k : ℤ, ‖f (x - ρ * (k : ℝ))‖ ^ 2)
        = ∑' k : ℤ,
            ‖fourierCoeffOn
              (a := (0 : ℝ)) (b := ρ⁻¹) hab F k‖ ^ 2 := by
          apply tsum_congr
          intro k
          rw [zakL2FrequencyFiber_fourierCoeffOn ρ hρ f x hc k]
    _ = (ρ⁻¹ - (0 : ℝ))⁻¹ •
          ∫ ω in (0 : ℝ)..ρ⁻¹,
            ‖F ω‖ ^ 2 := hparseval
    _ = ρ * (∫ ω in Set.Ioc (0 : ℝ) ρ⁻¹,
          ‖zakL2FrequencyFiber ρ hρ f x hc ω‖ ^ 2) := by
          rw [sub_zero, inv_inv]
          rw [intervalIntegral.integral_of_le hab.le]
          simp [F, smul_eq_mul]

/-- A.e. square-summability of the spatial sample fibers.  This is the
measure-theoretic input for constructing the true `L²` Zak frequency fiber for
arbitrary `L²` representatives. -/
def zakFiberSampleSqSummableAETarget (ρ : ℝ) : Prop :=
  ∀ f : ℝ → ℂ,
    MemLp f 2 (volume : Measure ℝ) →
      ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) ρ →
        Summable fun k : ℤ => ‖f (x - ρ * (k : ℝ))‖ ^ 2

/-- An `L²` function has integrable squared norm. -/
theorem integrable_norm_sq_of_memLp_two
    {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) (volume : Measure ℝ) := by
  simpa using hf.integrable_norm_pow (show (2 : ℕ) ≠ 0 by norm_num)

/-- Unit-scale interval-integral periodization for an integrable real function,
with the sign convention used by the Zak samples. -/
theorem realLineUnitPeriodizationIntervalHasSum_sub
    {Φ : ℝ → ℝ}
    (hΦ : Integrable Φ (volume : Measure ℝ)) :
    HasSum
      (fun k : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, Φ (x - (k : ℝ)))
      (∫ x : ℝ, Φ x) := by
  have hunit :
      HasSum
        (fun n : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, Φ (x + (n : ℝ)))
        (∫ x : ℝ, Φ x) := by
    simpa [intervalIntegral.integral_of_le zero_le_one] using
      hΦ.hasSum_intervalIntegral_comp_add_int
  have h := ((Equiv.neg ℤ).hasSum_iff
    (f := fun n : ℤ =>
      ∫ x in Set.Ioc (0 : ℝ) 1, Φ (x + (n : ℝ)))
    (a := ∫ x : ℝ, Φ x)).2 hunit
  simpa [Function.comp_def, sub_eq_add_neg] using h

/-- Termwise scaling for the periodization interval integrals. -/
theorem realLineScaledPeriodizationIntervalTerm
    (ρ : ℝ)
    (hρ : 0 < ρ)
    {Φ : ℝ → ℝ}
    (k : ℤ) :
    (∫ u in Set.Ioc (0 : ℝ) 1, ρ * Φ (ρ * (u - (k : ℝ)))) =
      ∫ x in Set.Ioc (0 : ℝ) ρ, Φ (x - ρ * (k : ℝ)) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [← intervalIntegral.integral_of_le hρ.le]
  calc
    (∫ u in (0 : ℝ)..1, ρ * Φ (ρ * (u - (k : ℝ))))
        = ρ * ∫ u in (0 : ℝ)..1, Φ (ρ * u - ρ * (k : ℝ)) := by
          rw [intervalIntegral.integral_const_mul]
          simp [mul_sub]
    _ = ∫ y in (0 : ℝ) - ρ * (k : ℝ)..ρ - ρ * (k : ℝ), Φ y := by
          simp [sub_eq_add_neg]
    _ = ∫ x in (0 : ℝ)..ρ, Φ (x - ρ * (k : ℝ)) := by
          simp [sub_eq_add_neg]

/-- Scaling the full real-line integral by a positive factor preserves the
integral after multiplying by the Jacobian. -/
theorem realLineScaledPeriodizationIntegral
    (ρ : ℝ)
    (hρ : 0 < ρ)
    {Φ : ℝ → ℝ} :
    (∫ u : ℝ, ρ * Φ (ρ * u)) = ∫ x : ℝ, Φ x := by
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ
  calc
    (∫ u : ℝ, ρ * Φ (ρ * u)) = ρ * ∫ u : ℝ, Φ (ρ * u) := by
      rw [integral_const_mul]
    _ = ρ * (|ρ⁻¹| * ∫ x : ℝ, Φ x) := by
      rw [Measure.integral_comp_mul_left]
      simp [smul_eq_mul]
    _ = ∫ x : ℝ, Φ x := by
      have habs : |ρ⁻¹| = ρ⁻¹ := abs_of_pos (inv_pos.mpr hρ)
      rw [habs]
      field_simp [hρ_ne]

/-- Positive-scale interval-integral periodization for integrable real
functions. -/
theorem realLineScaledPeriodizationIntervalHasSum_sub
    (ρ : ℝ)
    (hρ : 0 < ρ)
    {Φ : ℝ → ℝ}
    (hΦ : Integrable Φ (volume : Measure ℝ)) :
    HasSum
      (fun k : ℤ => ∫ x in Set.Ioc (0 : ℝ) ρ,
        Φ (x - ρ * (k : ℝ)))
      (∫ x : ℝ, Φ x) := by
  let Ψ : ℝ → ℝ := fun u => ρ * Φ (ρ * u)
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ
  have hΨ : Integrable Ψ (volume : Measure ℝ) := by
    dsimp [Ψ]
    exact (hΦ.comp_mul_left' hρ_ne).const_mul ρ
  have hunit := realLineUnitPeriodizationIntervalHasSum_sub (Φ := Ψ) hΨ
  simpa [Ψ, realLineScaledPeriodizationIntervalTerm ρ hρ,
    realLineScaledPeriodizationIntegral ρ hρ] using hunit

/-- Positive-scale a.e. square-summability of the Zak sample fibers. -/
theorem zakFiberSampleSqSummableAETarget_of_pos
    (ρ : ℝ)
    (hρ : 0 < ρ) :
    zakFiberSampleSqSummableAETarget ρ := by
  intro f hf
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) ρ)
  let Φ : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let F : ℤ → ℝ → ℝ := fun k x => Φ (x - ρ * (k : ℝ))
  have hΦ : Integrable Φ (volume : Measure ℝ) :=
    integrable_norm_sq_of_memLp_two hf
  have hF_int : ∀ k : ℤ, Integrable (F k) μ := by
    intro k
    dsimp [F, Φ, μ]
    have hglobal :
        Integrable
          (fun x : ℝ => ‖f (x - ρ * (k : ℝ))‖ ^ 2)
          (volume : Measure ℝ) := by
      simpa [sub_eq_add_neg] using hΦ.comp_add_right (-ρ * (k : ℝ))
    exact hglobal.mono_measure Measure.restrict_le_self
  have hsum_integral_norm :
      Summable fun k : ℤ => ∫ x, ‖F k x‖ ∂μ := by
    have hhas := realLineScaledPeriodizationIntervalHasSum_sub ρ hρ hΦ
    have hhas_norm :
        HasSum
          (fun k : ℤ => ∫ x in Set.Ioc (0 : ℝ) ρ, ‖F k x‖)
          (∫ x : ℝ, Φ x) := by
      simpa [F, Φ, Real.norm_of_nonneg (sq_nonneg _)] using hhas
    simpa [μ] using hhas_norm.summable
  have h_eLp :
      (∑' k : ℤ, eLpNorm (F k) 1 μ) ≠ ⊤ := by
    have heq : (fun k : ℤ => eLpNorm (F k) 1 μ) =
        fun k : ℤ => ENNReal.ofReal (∫ x, ‖F k x‖ ∂μ) := by
      funext k
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact (ofReal_integral_norm_eq_lintegral_enorm (hF_int k)).symm
    rw [heq]
    exact hsum_integral_norm.tsum_ofReal_ne_top
  have hae_restrict :
      ∀ᵐ x ∂μ, Summable fun k : ℤ => ‖F k x‖ :=
    summable_norm_of_tsum_eLpNorm_ne_top (show (1 : ENNReal) ≤ 1 by rfl)
      (fun k => (hF_int k).aestronglyMeasurable) h_eLp
  rw [ae_restrict_iff' measurableSet_Ioc] at hae_restrict
  filter_upwards [hae_restrict] with x hx hx_mem
  have hx' := hx hx_mem
  simpa [F, Φ, Real.norm_of_nonneg (sq_nonneg _)] using hx'

end Zak
