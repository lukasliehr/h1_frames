import LeanCode.GeneralLattice.LatticeReduction

open MeasureTheory
open scoped BigOperators ENNReal

namespace LyubarskiiNes.GeneralLattice

/-- The unimodular quadratic phase implementing a lower symplectic shear. -/
noncomputable def chirpPhase (η t : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2)

@[simp] lemma norm_chirpPhase (η t : ℝ) : ‖chirpPhase η t‖ = 1 := by
  unfold chirpPhase
  have harg :
      (Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2 =
        ((Real.pi * η * t ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem memLp_chirpFun (η : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun t : ℝ => chirpPhase η t * (f : ℝ → ℂ) t)
      2 (volume : Measure ℝ) := by
  have hf := Lp.memLp f
  refine ⟨?_, ?_⟩
  · exact (Continuous.aestronglyMeasurable (by
      unfold chirpPhase
      continuity)).mul hf.1
  · have heq :
        eLpNorm (fun t : ℝ => chirpPhase η t * (f : ℝ → ℂ) t) 2 volume =
          eLpNorm (f : ℝ → ℂ) 2 volume :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun t => by
        rw [norm_mul, norm_chirpPhase, one_mul])
    exact heq.trans_lt hf.2

/-- Quadratic-phase multiplication on `L²(ℝ)`. -/
noncomputable def chirpLp (η : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_chirpFun η f).toLp

lemma chirpLp_coe_ae (η : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (chirpLp η f : ℝ → ℂ) =ᵐ[volume]
      fun t => chirpPhase η t * (f : ℝ → ℂ) t :=
  (memLp_chirpFun η f).coeFn_toLp

lemma chirpLp_add (η : ℝ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    chirpLp η (f + g) = chirpLp η f + chirpLp η g := by
  apply Lp.ext
  filter_upwards [chirpLp_coe_ae η (f + g), chirpLp_coe_ae η f,
    chirpLp_coe_ae η g, Lp.coeFn_add f g,
    Lp.coeFn_add (chirpLp η f) (chirpLp η g)] with t hfg hf hg hadd hsum
  rw [hfg, hsum, hadd]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

lemma chirpLp_smul (η : ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    chirpLp η (c • f) = c • chirpLp η f := by
  apply Lp.ext
  filter_upwards [chirpLp_coe_ae η (c • f), chirpLp_coe_ae η f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (chirpLp η f)] with t hcf hf hsmul hres
  rw [hcf, hres, hsmul]
  simp only [Pi.smul_apply]
  rw [hf]
  ring

@[simp] lemma norm_chirpLp (η : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖chirpLp η f‖ = ‖f‖ := by
  unfold chirpLp
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun t => by
    rw [norm_mul, norm_chirpPhase, one_mul])

noncomputable def chirpLinearIsometry (η : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := chirpLp η
  map_add' := chirpLp_add η
  map_smul' := chirpLp_smul η
  norm_map' := norm_chirpLp η

private lemma chirpPhase_neg_mul (η t : ℝ) :
    chirpPhase η t * chirpPhase (-η) t = 1 := by
  unfold chirpPhase
  rw [← Complex.exp_add]
  convert Complex.exp_zero
  push_cast
  ring

/-- The chirp operator is unitary; its inverse is the chirp with parameter
`-η`. -/
noncomputable def chirpLinearIsometryEquiv (η : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (chirpLinearIsometry η) (by
    intro f
    refine ⟨chirpLp (-η) f, ?_⟩
    change chirpLp η (chirpLp (-η) f) = f
    apply Lp.ext
    filter_upwards [chirpLp_coe_ae η (chirpLp (-η) f),
      chirpLp_coe_ae (-η) f] with t hout hin
    rw [hout, hin]
    have hphase : chirpPhase η t * chirpPhase (-η) t = 1 :=
      chirpPhase_neg_mul η t
    rw [← mul_assoc, hphase, one_mul])

/-- The normalized dilation `f(t) ↦ ν⁻¹² f(t/ν)`. -/
noncomputable def dilationFun (ν : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  ((Real.sqrt ν : ℂ)⁻¹) * (f : ℝ → ℂ) (t / ν)

private lemma Lp_norm_sq_eq_integral_real
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖(f : ℝ → ℂ) t‖ ^ 2 := by
  have hint : Integrable (fun t : ℝ => ‖(f : ℝ → ℂ) t‖ ^ 2) volume :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) hint.1,
    Lp.norm_def, ← ENNReal.toReal_pow]
  congr 1
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat,
    ← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]
  refine lintegral_congr (fun t => ?_)
  rw [ENNReal.ofReal_pow (norm_nonneg ((f : ℝ → ℂ) t)), ofReal_norm,
    ← ENNReal.rpow_natCast ‖(f : ℝ → ℂ) t‖ₑ 2, Nat.cast_ofNat]

private lemma dilationScalar_norm_sq {ν : ℝ} (hν : 0 < ν) :
    ‖((Real.sqrt ν : ℂ)⁻¹)‖ ^ 2 = ν⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hν),
    inv_pow, Real.sq_sqrt hν.le]

private lemma quasiMeasurePreserving_div_const {ν : ℝ} (hν : ν ≠ 0) :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun t : ℝ => t / ν) volume volume := by
  simpa [div_eq_inv_mul, smul_eq_mul, mul_comm] using
    (MeasureTheory.Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hν) :
      MeasureTheory.Measure.QuasiMeasurePreserving (fun t : ℝ => ν⁻¹ • t) volume volume)

private theorem memLp_dilationFun {ν : ℝ} (hν : 0 < ν)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (dilationFun ν f) 2 (volume : Measure ℝ) := by
  have hf := Lp.memLp f
  have hmeas : AEStronglyMeasurable (dilationFun ν f) volume := by
    unfold dilationFun
    exact (aestronglyMeasurable_const.mul
      (hf.1.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_div_const (ne_of_gt hν))))
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have hbase : Integrable (fun t : ℝ => ‖(f : ℝ → ℂ) t‖ ^ 2) volume :=
    hf.integrable_norm_pow (by norm_num)
  have hcomp : Integrable (fun t : ℝ => ‖(f : ℝ → ℂ) (t / ν)‖ ^ 2) volume :=
    hbase.comp_div (ne_of_gt hν)
  exact (hcomp.const_mul ν⁻¹).congr (Filter.Eventually.of_forall fun t => by
    unfold dilationFun
    change ν⁻¹ * ‖(f : ℝ → ℂ) (t / ν)‖ ^ 2 =
      ‖(Real.sqrt ν : ℂ)⁻¹ * (f : ℝ → ℂ) (t / ν)‖ ^ 2
    rw [norm_mul, mul_pow, dilationScalar_norm_sq hν])

noncomputable def dilationLp (ν : ℝ) (hν : 0 < ν)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_dilationFun hν f).toLp

lemma dilationLp_coe_ae (ν : ℝ) (hν : 0 < ν)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dilationLp ν hν f : ℝ → ℂ) =ᵐ[volume] dilationFun ν f :=
  (memLp_dilationFun hν f).coeFn_toLp

lemma dilationLp_add (ν : ℝ) (hν : 0 < ν)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    dilationLp ν hν (f + g) = dilationLp ν hν f + dilationLp ν hν g := by
  apply Lp.ext
  have hqmp := quasiMeasurePreserving_div_const (ne_of_gt hν)
  filter_upwards [dilationLp_coe_ae ν hν (f + g), dilationLp_coe_ae ν hν f,
    dilationLp_coe_ae ν hν g, Lp.coeFn_add f g,
    hqmp.ae_eq (Lp.coeFn_add f g),
    Lp.coeFn_add (dilationLp ν hν f) (dilationLp ν hν g)] with
      t hout hf hg _hadd hadd hres
  rw [hout, hres]
  unfold dilationFun
  simp only [Function.comp_apply] at hadd
  rw [hadd]
  simp only [Pi.add_apply, hf, hg]
  unfold dilationFun
  ring

lemma dilationLp_smul (ν : ℝ) (hν : 0 < ν) (c : ℂ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilationLp ν hν (c • f) = c • dilationLp ν hν f := by
  apply Lp.ext
  have hqmp := quasiMeasurePreserving_div_const (ne_of_gt hν)
  filter_upwards [dilationLp_coe_ae ν hν (c • f), dilationLp_coe_ae ν hν f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (dilationLp ν hν f),
    hqmp.ae_eq (Lp.coeFn_smul c f)] with
      t hout hf _hsmul hres ht_smul
  rw [hout, hres]
  unfold dilationFun
  simp only [Function.comp_apply] at ht_smul
  rw [ht_smul]
  simp only [Pi.smul_apply, hf]
  unfold dilationFun
  ring

@[simp] lemma norm_dilationLp (ν : ℝ) (hν : 0 < ν)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖dilationLp ν hν f‖ = ‖f‖ := by
  have hsquare : ‖dilationLp ν hν f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [Lp_norm_sq_eq_integral_real, Lp_norm_sq_eq_integral_real]
    have hae := dilationLp_coe_ae ν hν f
    have hi : (∫ t : ℝ, ‖(dilationLp ν hν f : ℝ → ℂ) t‖ ^ 2) =
        ∫ t : ℝ, ‖dilationFun ν f t‖ ^ 2 :=
      integral_congr_ae (hae.mono fun t ht => congrArg (fun z : ℂ => ‖z‖ ^ 2) ht)
    rw [hi]
    simp_rw [dilationFun, norm_mul, mul_pow, dilationScalar_norm_sq hν]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_div
        (fun t : ℝ => ‖(f : ℝ → ℂ) t‖ ^ 2) ν]
    simp [abs_of_pos hν, smul_eq_mul]
    field_simp [ne_of_gt hν]
  nlinarith [norm_nonneg (dilationLp ν hν f), norm_nonneg f]

noncomputable def dilationLinearIsometry (ν : ℝ) (hν : 0 < ν) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := dilationLp ν hν
  map_add' := dilationLp_add ν hν
  map_smul' := dilationLp_smul ν hν
  norm_map' := norm_dilationLp ν hν

/-- The normalized dilation is a unitary operator. -/
noncomputable def dilationLinearIsometryEquiv (ν : ℝ) (hν : 0 < ν) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (dilationLinearIsometry ν hν) (by
    intro f
    let hνinv : 0 < ν⁻¹ := inv_pos.mpr hν
    refine ⟨dilationLp ν⁻¹ hνinv f, ?_⟩
    change dilationLp ν hν (dilationLp ν⁻¹ hνinv f) = f
    apply Lp.ext
    have hqmp := quasiMeasurePreserving_div_const (ne_of_gt hν)
    filter_upwards [dilationLp_coe_ae ν hν (dilationLp ν⁻¹ hνinv f),
      dilationLp_coe_ae ν⁻¹ hνinv f,
      hqmp.ae_eq (dilationLp_coe_ae ν⁻¹ hνinv f)] with
        t hout _hin hin
    rw [hout]
    unfold dilationFun
    simp only [Function.comp_apply] at hin
    rw [hin]
    unfold dilationFun
    rw [Real.sqrt_inv]
    rw [Complex.ofReal_inv, inv_inv]
    have hs : Real.sqrt ν ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hν)
    field_simp [ne_of_gt hν, hs])

/-- Upper-half-plane parameter after normalized dilation. -/
noncomputable def dilatedTau (ν : ℝ) (τ : ℂ) : ℂ :=
  τ / (ν : ℂ) ^ 2

lemma dilatedTau_im_pos {ν : ℝ} (hν : 0 < ν) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (dilatedTau ν τ).im := by
  unfold dilatedTau
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hcast : ((ν : ℂ) ^ 2) = ((ν ^ 2 : ℝ) : ℂ) := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hcast]
  have him : (τ / ((ν ^ 2 : ℝ) : ℂ)).im = τ.im / ν ^ 2 := by
    rw [Complex.div_im]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    field_simp [hν0]
  rw [him]
  exact div_pos hτ (sq_pos_of_pos hν)

/-- Nonzero scalar relating the normalized dilation of `generalizedH1 τ`
to the normalized representative `generalizedH1 (τ/ν²)`. -/
noncomputable def dilationH1Scale (ν : ℝ) : ℂ :=
  (Real.sqrt ν : ℂ)⁻¹ * (ν : ℂ)⁻¹

lemma dilationH1Scale_ne_zero {ν : ℝ} (hν : 0 < ν) :
    dilationH1Scale ν ≠ 0 := by
  exact mul_ne_zero
    (inv_ne_zero (by exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hν)))
    (inv_ne_zero (by exact_mod_cast ne_of_gt hν))

lemma dilation_generalizedH1_pointwise
    {ν : ℝ} (hν : 0 < ν) (τ : ℂ) (t : ℝ) :
    (Real.sqrt ν : ℂ)⁻¹ * generalizedH1 τ (t / ν) =
      dilationH1Scale ν * generalizedH1 (dilatedTau ν τ) t := by
  have hνR : ν ≠ 0 := ne_of_gt hν
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hνR
  unfold generalizedH1 dilationH1Scale dilatedTau
  have harg :
      (Real.pi : ℂ) * Complex.I * τ * ((t / ν : ℝ) : ℂ) ^ 2 =
        (Real.pi : ℂ) * Complex.I * (τ / (ν : ℂ) ^ 2) * (t : ℂ) ^ 2 := by
    push_cast
    field_simp [hνC]
  rw [harg]
  push_cast
  field_simp [hνC]

lemma dilationLinearIsometryEquiv_generalizedH1
    (ν : ℝ) (hν : 0 < ν) {τ : ℂ} (hτ : 0 < τ.im) :
    dilationLinearIsometryEquiv ν hν (generalizedH1Lp τ hτ) =
      dilationH1Scale ν •
        generalizedH1Lp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ) := by
  change dilationLp ν hν (generalizedH1Lp τ hτ) = _
  apply Lp.ext
  have hqmp := quasiMeasurePreserving_div_const (ne_of_gt hν)
  have hsource : (generalizedH1Lp τ hτ : ℝ → ℂ) =ᵐ[volume] generalizedH1 τ := by
    unfold generalizedH1Lp
    exact (memLp_generalizedH1 hτ).coeFn_toLp
  have htarget :
      (generalizedH1Lp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ) : ℝ → ℂ) =ᵐ[volume]
        generalizedH1 (dilatedTau ν τ) := by
    unfold generalizedH1Lp
    exact (memLp_generalizedH1 (dilatedTau_im_pos hν hτ)).coeFn_toLp
  filter_upwards [dilationLp_coe_ae ν hν (generalizedH1Lp τ hτ),
    hqmp.ae_eq hsource, htarget,
    Lp.coeFn_smul (dilationH1Scale ν)
      (generalizedH1Lp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ))] with
      t hout hsrc htarg hsmul
  rw [hout]
  unfold dilationFun
  simp only [Function.comp_apply] at hsrc
  rw [hsrc, hsmul, Pi.smul_apply, htarg]
  exact dilation_generalizedH1_pointwise hν τ t

/-- Exact dilation covariance for generalized time-frequency atoms. -/
lemma dilation_generalizedH1LatticeElement_pointwise
    {ν : ℝ} (hν : 0 < ν) (τ : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) (t : ℝ) :
    (Real.sqrt ν : ℂ)⁻¹ * generalizedH1LatticeElement τ M m n (t / ν) =
      dilationH1Scale ν *
        generalizedH1LatticeElement (dilatedTau ν τ)
          (symplecticDilationMatrix ν * M) m n t := by
  let x := latticeTime M m n
  let ω := latticeFrequency M m n
  unfold generalizedH1LatticeElement
  rw [show latticeTime (symplecticDilationMatrix ν * M) m n = ν * x by simp [x],
    show latticeFrequency (symplecticDilationMatrix ν * M) m n = ν⁻¹ * ω by simp [ω]]
  have hνR : ν ≠ 0 := ne_of_gt hν
  have hmod :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * ((t / ν : ℝ) : ℂ)) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((ν⁻¹ * ω : ℝ) : ℂ) * (t : ℂ)) := by
    congr 1
    push_cast
    field_simp [hνR]
  rw [hmod]
  have harg : t / ν - x = (t - ν * x) / ν := by field_simp
  rw [harg]
  calc
    (Real.sqrt ν : ℂ)⁻¹ *
          (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((ν⁻¹ * ω : ℝ) : ℂ) * (t : ℂ)) *
            generalizedH1 τ ((t - ν * x) / ν)) =
        Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((ν⁻¹ * ω : ℝ) : ℂ) * (t : ℂ)) *
          ((Real.sqrt ν : ℂ)⁻¹ * generalizedH1 τ ((t - ν * x) / ν)) := by ring
    _ = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((ν⁻¹ * ω : ℝ) : ℂ) * (t : ℂ)) *
          (dilationH1Scale ν * generalizedH1 (dilatedTau ν τ) (t - ν * x)) := by
            rw [dilation_generalizedH1_pointwise hν τ]
    _ = dilationH1Scale ν *
          (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((ν⁻¹ * ω : ℝ) : ℂ) * (t : ℂ)) *
            generalizedH1 (dilatedTau ν τ) (t - ν * x)) := by ring

lemma dilationLinearIsometryEquiv_generalizedH1LatticeElementLp
    (ν : ℝ) (hν : 0 < ν) {τ : ℂ} (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    dilationLinearIsometryEquiv ν hν (generalizedH1LatticeElementLp τ hτ M m n) =
      dilationH1Scale ν •
        generalizedH1LatticeElementLp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ)
          (symplecticDilationMatrix ν * M) m n := by
  change dilationLp ν hν (generalizedH1LatticeElementLp τ hτ M m n) = _
  apply Lp.ext
  have hqmp := quasiMeasurePreserving_div_const (ne_of_gt hν)
  have hsource :
      (generalizedH1LatticeElementLp τ hτ M m n : ℝ → ℂ) =ᵐ[volume]
        generalizedH1LatticeElement τ M m n := by
    unfold generalizedH1LatticeElementLp
    exact (memLp_generalizedH1LatticeElement hτ M m n).coeFn_toLp
  have htarget :
      (generalizedH1LatticeElementLp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ)
        (symplecticDilationMatrix ν * M) m n : ℝ → ℂ) =ᵐ[volume]
        generalizedH1LatticeElement (dilatedTau ν τ)
          (symplecticDilationMatrix ν * M) m n := by
    unfold generalizedH1LatticeElementLp
    exact (memLp_generalizedH1LatticeElement (dilatedTau_im_pos hν hτ)
      (symplecticDilationMatrix ν * M) m n).coeFn_toLp
  filter_upwards [dilationLp_coe_ae ν hν (generalizedH1LatticeElementLp τ hτ M m n),
    hqmp.ae_eq hsource, htarget,
    Lp.coeFn_smul (dilationH1Scale ν)
      (generalizedH1LatticeElementLp (dilatedTau ν τ) (dilatedTau_im_pos hν hτ)
        (symplecticDilationMatrix ν * M) m n)] with t hout hsrc htarg hsmul
  rw [hout]
  unfold dilationFun
  simp only [Function.comp_apply] at hsrc
  rw [hsrc, hsmul, Pi.smul_apply, htarg]
  exact dilation_generalizedH1LatticeElement_pointwise hν τ M m n t

theorem isGeneralizedGaborFrameForLattice_dilation_iff
    (ν : ℝ) (hν : 0 < ν) (τ : ℂ) (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice (dilatedTau ν τ) (dilatedTau_im_pos hν hτ)
        (symplecticDilationMatrix ν * M) ↔
      IsGeneralizedGaborFrameForLattice τ hτ M := by
  rw [isGeneralizedGaborFrameForLattice_iff_isFrameFamily,
    isGeneralizedGaborFrameForLattice_iff_isFrameFamily]
  let U := dilationLinearIsometryEquiv ν hν
  let oldFamily := generalizedH1LatticeElementLp τ hτ M
  let newFamily := generalizedH1LatticeElementLp (dilatedTau ν τ)
    (dilatedTau_im_pos hν hτ) (symplecticDilationMatrix ν * M)
  have hcov : (fun m n => U (oldFamily m n)) =
      fun m n => dilationH1Scale ν • newFamily m n := by
    funext m n
    exact dilationLinearIsometryEquiv_generalizedH1LatticeElementLp ν hν hτ M m n
  rw [← isFrameFamily_smul newFamily (dilationH1Scale ν) (dilationH1Scale_ne_zero hν),
    ← hcov]
  exact isFrameFamily_linearIsometryEquiv U oldFamily

/-- On concrete generalized Hermite windows, the `L²` chirp is the expected
pointwise chirp, hence it adds the real shear parameter to `τ`. -/
lemma chirpLinearIsometryEquiv_generalizedH1
    (η : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    chirpLinearIsometryEquiv η (generalizedH1Lp τ hτ) =
      generalizedH1Lp (τ + η) (by simpa using hτ) := by
  change chirpLp η (generalizedH1Lp τ hτ) =
    generalizedH1Lp (τ + η) (by simpa using hτ)
  apply Lp.ext
  have hleft : (generalizedH1Lp τ hτ : ℝ → ℂ) =ᵐ[volume] generalizedH1 τ := by
    unfold generalizedH1Lp
    exact (memLp_generalizedH1 hτ).coeFn_toLp
  have hright :
      (generalizedH1Lp (τ + η) (by simpa using hτ) : ℝ → ℂ) =ᵐ[volume]
        generalizedH1 (τ + η) := by
    unfold generalizedH1Lp
    exact (memLp_generalizedH1 (by simpa using hτ : 0 < (τ + η).im)).coeFn_toLp
  filter_upwards [chirpLp_coe_ae η (generalizedH1Lp τ hτ), hleft, hright] with
      t hchirp htleft htright
  rw [hchirp, htleft, htright]
  exact congrFun (chirp_generalizedH1 η τ) t

/-- Pointwise covariance of a time-frequency atom under a lower shear.  The
remaining scalar is unimodular and therefore irrelevant to frame bounds. -/
lemma chirp_generalizedH1LatticeElement
    (η : ℝ) (τ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    chirp η (generalizedH1LatticeElement τ M m n) =
      fun t => chirpPhase (-η) (latticeTime M m n) *
        generalizedH1LatticeElement (τ + η) (lowerShearMatrix η * M) m n t := by
  funext t
  let x : ℝ := latticeTime M m n
  let ω : ℝ := latticeFrequency M m n
  have hexp :
      chirpPhase η t *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) =
        chirpPhase (-η) x *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((η * x + ω : ℝ) : ℂ) * (t : ℂ)) *
          chirpPhase η (t - x) := by
    unfold chirpPhase
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold chirp generalizedH1LatticeElement
  change chirpPhase η t *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
        generalizedH1 τ (t - x)) = _
  rw [latticeTime_lowerShearMatrix_mul, latticeFrequency_lowerShearMatrix_mul]
  change _ = chirpPhase (-η) x *
    (Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((η * x + ω : ℝ) : ℂ) * (t : ℂ)) *
      generalizedH1 (τ + η) (t - x))
  rw [← congrFun (chirp_generalizedH1 η τ) (t - x)]
  unfold chirp
  calc
    chirpPhase η t *
          (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ)) *
            generalizedH1 τ (t - x)) =
        (chirpPhase η t *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))) *
          generalizedH1 τ (t - x) := by ring
    _ = (chirpPhase (-η) x *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((η * x + ω : ℝ) : ℂ) * (t : ℂ)) *
          chirpPhase η (t - x)) * generalizedH1 τ (t - x) := by rw [hexp]
    _ = chirpPhase (-η) x *
          (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((η * x + ω : ℝ) : ℂ) * (t : ℂ)) *
            (Complex.exp
                ((Real.pi : ℂ) * Complex.I * (η : ℂ) * ((t - x : ℝ) : ℂ) ^ 2) *
              generalizedH1 τ (t - x))) := by
        unfold chirpPhase
        ring

lemma chirpLinearIsometryEquiv_generalizedH1LatticeElementLp
    (η : ℝ) {τ : ℂ} (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    chirpLinearIsometryEquiv η (generalizedH1LatticeElementLp τ hτ M m n) =
      chirpPhase (-η) (latticeTime M m n) •
        generalizedH1LatticeElementLp (τ + η) (by simpa using hτ)
          (lowerShearMatrix η * M) m n := by
  change chirpLp η (generalizedH1LatticeElementLp τ hτ M m n) = _
  apply Lp.ext
  have hatom :
      (generalizedH1LatticeElementLp τ hτ M m n : ℝ → ℂ) =ᵐ[volume]
        generalizedH1LatticeElement τ M m n := by
    unfold generalizedH1LatticeElementLp
    exact (memLp_generalizedH1LatticeElement hτ M m n).coeFn_toLp
  have htarget :
      (generalizedH1LatticeElementLp (τ + η) (by simpa using hτ)
        (lowerShearMatrix η * M) m n : ℝ → ℂ) =ᵐ[volume]
        generalizedH1LatticeElement (τ + η) (lowerShearMatrix η * M) m n := by
    unfold generalizedH1LatticeElementLp
    exact (memLp_generalizedH1LatticeElement (by simpa using hτ)
      (lowerShearMatrix η * M) m n).coeFn_toLp
  filter_upwards [chirpLp_coe_ae η (generalizedH1LatticeElementLp τ hτ M m n),
    hatom, htarget,
    Lp.coeFn_smul (chirpPhase (-η) (latticeTime M m n))
      (generalizedH1LatticeElementLp (τ + η) (by simpa using hτ)
        (lowerShearMatrix η * M) m n)] with t hchirp hsource htarg hsmul
  rw [hchirp, hsource, hsmul, Pi.smul_apply, htarg]
  exact congrFun (chirp_generalizedH1LatticeElement η τ M m n) t

/-- Metaplectic covariance for the lower-shear generator, at the level of the
actual frame predicates. -/
theorem isGeneralizedGaborFrameForLattice_lowerShear_iff
    (η : ℝ) (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice (τ + η) (by simpa using hτ)
        (lowerShearMatrix η * M) ↔
      IsGeneralizedGaborFrameForLattice τ hτ M := by
  rw [isGeneralizedGaborFrameForLattice_iff_isFrameFamily,
    isGeneralizedGaborFrameForLattice_iff_isFrameFamily]
  let U := chirpLinearIsometryEquiv η
  let oldFamily := generalizedH1LatticeElementLp τ hτ M
  let newFamily := generalizedH1LatticeElementLp (τ + η) (by simpa using hτ)
    (lowerShearMatrix η * M)
  have hcov : ∀ m n, U (oldFamily m n) =
      chirpPhase (-η) (latticeTime M m n) • newFamily m n := by
    intro m n
    exact chirpLinearIsometryEquiv_generalizedH1LatticeElementLp η hτ M m n
  have hcongr : IsFrameFamily (fun m n => U (oldFamily m n)) ↔ IsFrameFamily newFamily := by
    apply isFrameFamily_congr
    intro f m n
    rw [hcov]
    simp [norm_chirpPhase]
  rw [← hcongr]
  exact isFrameFamily_linearIsometryEquiv U oldFamily

end LyubarskiiNes.GeneralLattice
