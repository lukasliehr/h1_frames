import LeanCode.GeneralLattice.GeneralizedBounds

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal FourierTransform

namespace LyubarskiiNes.GeneralLattice.GeneralizedCriterion

open LyubarskiiNes.RationalDensity

variable {τ : ℂ} {hτ : 0 < τ.im}

noncomputable def generalizedProductCoeffEnergy (α β : ℝ)
    (x : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  ∑' mn : ℤ × ℤ,
    ‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2

noncomputable def generalizedRationalPositiveGammaMatrixEnergy
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β)
    (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2)
    (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) : ℝ :=
  rationalZakEta α p q * rationalZakGamma α q *
    ‖generalizedRationalZakMatrix τ α p q z *ᵥ
      rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2

lemma rationalZakMatrix_mulVec_apply {α : ℝ} {p q : ℕ} (z : ℝ × ℝ)
    (w : Fin p → ℂ) (t : Fin q) :
    (generalizedRationalZakMatrix τ α p q z *ᵥ w) t =
      ∑ s' : Fin p,
        (starRingEnd ℂ) (generalizedRationalZakPMatrix τ α p q z s' t) * w s' := by
  rw [generalizedRationalZakMatrix]
  simp [Matrix.mulVec, dotProduct]

/-- **The window's conjugate is the `h₁` γ-Zak transform.** A window `P` on `(0,γ⁻¹]`
whose `i`-th Fourier coefficient is the Gaussian sample `generalizedH1 τ(b₀+γi)` (i.e. one
produced by `exists_window_P` at base `b₀`) has `conj P` a.e. equal to
`zakTransform γ generalizedH1 τ b₀`.  Proof: both are `L²`; their coefficients agree — for
`conj P` the coefficient flips index (`fourierCoeffOn_conj`) and conjugates the real
Gaussian sample, matching `fourierCoeffOn_zakTransform_eq_sample`. -/
lemma window_conj_ae_eq_zakTransform_h1 {γ : ℝ} (hτ : 0 < τ.im)
    (hγ : 0 < γ) (b₀ : ℝ) (P : ℝ → ℂ)
    (hPmem : MemLp (fun ξ => (starRingEnd ℂ) (P ξ)) 2
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)))
    (hP : ∀ i : ℤ, fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P i
      = (starRingEnd ℂ) (generalizedH1 τ (b₀ + γ * (i : ℝ)))) :
    (fun ξ => (starRingEnd ℂ) (P ξ))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)]
      (fun ξ => Zak.zakTransform γ (generalizedH1 τ) b₀ ξ) := by
  have hsum : Summable fun k : ℤ => ‖generalizedH1 τ (b₀ - γ * (k : ℝ))‖ :=
    summable_norm_generalizedH1_samples hτ γ hγ b₀
  refine ae_eq_of_fourierCoeffOn_eq hγ hPmem (memLp_zakTransform hγ hsum) (fun i => ?_)
  rw [fourierCoeffOn_conj hγ P i, hP (-i),
    fourierCoeffOn_zakTransform_eq_sample hγ hsum i]
  rw [Complex.conj_conj]
  congr 1; push_cast; ring

/-- **The dense `X`-factor is the conjugate `φ` γ-Zak transform.** For a compactly
sampled window `φ` (samples `b ↦ φ(x+bγ)` supported on the finite set `u`), the dense
side's finite trigonometric factor `∑_{b∈u} conj(φ(x+bγ))·exp(2πiγbξ)` equals
`conj(zakTransform γ φ x ξ)`.  Proof: `zakTransform` is a `tsum` over `k`; collapse to
the finite support `-u`, conjugate the finite sum, and reindex `k = −b`. -/
lemma conj_zakTransform_compactSample {γ : ℝ} {φ : ℝ → ℂ} (x ξ : ℝ)
    (u : Finset ℤ) (hu : ∀ b ∉ u, φ (x + (b : ℝ) * γ) = 0) :
    (starRingEnd ℂ) (Zak.zakTransform γ φ x ξ)
      = ∑ b ∈ u, (starRingEnd ℂ) (φ (x + (b : ℝ) * γ)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I * ((γ : ℂ) * (b : ℂ) * (ξ : ℂ))) := by
  rw [Zak.zakTransform_apply,
    tsum_eq_sum (s := u.image Neg.neg) (fun k hk => by
      have hkn : (-k) ∉ u := fun h => hk (Finset.mem_image.mpr ⟨-k, h, neg_neg k⟩)
      have hz : φ (x - γ * (k : ℝ)) = 0 := by
        have h0 := hu (-k) hkn
        rwa [show x + ((-k : ℤ) : ℝ) * γ = x - γ * (k : ℝ) from by push_cast; ring] at h0
      rw [hz, zero_mul]),
    map_sum, Finset.sum_image (fun a _ b _ h => neg_injective h)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul]
  have ha : x - γ * (((-b : ℤ)) : ℝ) = x + ((b : ℤ) : ℝ) * γ := by push_cast; ring
  have he : (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ)
        * (((-b : ℤ)) : ℂ) * (ξ : ℂ)))
      = Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I * ((γ : ℂ) * ((b : ℤ) : ℂ) * (ξ : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_intCast]
    push_cast; ring
  rw [ha, he]

/-- **The window `P`-object (B3 input).** For any base point `b₀`, there is an
`L²` function `P` on `(0,γ⁻¹]` whose conjugate is `MemLp` (the `hP` hypothesis of
`gamma_step34`) and whose `i`-th interval Fourier coefficient is the Gaussian
window sample `generalizedH1 τ (b₀ + iγ)`.  These are exactly the window samples in
the per-strip γ-convolution produced by `inner_periodization_p_strip_h1`, so this
supplies the `P` consumed by the ξ-side identity.  Built by Riesz–Fischer from
the (Gaussian-decay) square-summable samples via `Zak.zakL2FrequencyFiber`. -/
lemma exists_window_P {γ : ℝ} (hτ : 0 < τ.im) (hγ : 0 < γ) (b₀ : ℝ) :
    ∃ P : ℝ → ℂ,
      MemLp (fun ξ => (starRingEnd ℂ) (P ξ)) 2
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)) ∧
      ∀ i : ℤ,
        fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P i
          = (starRingEnd ℂ) (generalizedH1 τ (b₀ + γ * (i : ℝ))) := by
  set f : ℝ → ℂ := fun y => (starRingEnd ℂ) (generalizedH1 τ (b₀ - y)) with hf
  have hc : Summable fun k : ℤ => ‖f (0 - γ * (k : ℝ))‖ ^ 2 := by
    have hbase := summable_sq_norm_generalizedH1_samples hτ γ hγ b₀
    have h2 := hbase.comp_injective (neg_injective)
    refine h2.congr (fun k => ?_)
    change ‖generalizedH1 τ (b₀ - γ * ((-k : ℤ) : ℝ))‖ ^ 2 =
      ‖star (generalizedH1 τ (b₀ - (0 - γ * (k : ℝ))))‖ ^ 2
    rw [norm_star]
    congr 2
    push_cast; ring
  have hPmem : MemLp (fun ξ => Zak.zakL2FrequencyFiber γ hγ f 0 hc ξ) 2
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)) :=
    Lp.memLp (Zak.zakL2FrequencyFiber γ hγ f 0 hc)
  refine ⟨fun ξ => Zak.zakL2FrequencyFiber γ hγ f 0 hc ξ, ?_, ?_⟩
  · have hstar : MemLp (fun ξ => star (Zak.zakL2FrequencyFiber γ hγ f 0 hc ξ)) 2
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)) := by
      refine ⟨hPmem.aestronglyMeasurable.star, ?_⟩
      rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ξ => norm_star _)]
      exact hPmem.2
    exact hstar
  · intro i
    rw [Zak.zakL2FrequencyFiber_fourierCoeffOn γ hγ f 0 hc i]
    simp only [hf]
    congr 1
    ring

/-- For a compactly supported `φ` and `γ > 0`, the γ-spaced samples
`b ↦ φ(base + bγ)` vanish outside a finite index set (only finitely many samples
land in the compact support). -/
lemma exists_finset_sample_support {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℂ}
    (hφ : HasCompactSupport φ) (base : ℝ) :
    ∃ u : Finset ℤ, ∀ b ∉ u, φ (base + (b : ℝ) * γ) = 0 := by
  obtain ⟨R, _hR0, hR⟩ := hφ.exists_pos_le_norm
  refine ⟨Finset.Icc (-(⌈(R + |base|) * γ⁻¹⌉₊ : ℤ)) (⌈(R + |base|) * γ⁻¹⌉₊ : ℤ), ?_⟩
  intro b hb
  apply hR (base + (b : ℝ) * γ)
  have hbInt : (⌈(R + |base|) * γ⁻¹⌉₊ : ℤ) + 1 ≤ |b| := by
    rw [Finset.mem_Icc] at hb
    rw [Int.abs_eq_natAbs]
    omega
  have hbabs : ((⌈(R + |base|) * γ⁻¹⌉₊ : ℝ)) + 1 ≤ |(b : ℝ)| := by
    have hcast : (((⌈(R + |base|) * γ⁻¹⌉₊ : ℤ) + 1 : ℤ) : ℝ) ≤ ((|b| : ℤ) : ℝ) := by
      exact_mod_cast hbInt
    rwa [Int.cast_abs, Int.cast_add, Int.cast_one, Int.cast_natCast] at hcast
  have hceil : (R + |base|) * γ⁻¹ ≤ (⌈(R + |base|) * γ⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : (R + |base|) * γ⁻¹ ≤ |(b : ℝ)| := by linarith
  have hk3 : R + |base| ≤ |(b : ℝ)| * γ := by
    have h := mul_le_mul_of_nonneg_right hk2 (le_of_lt hγ)
    rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hγ), mul_one] at h
  have htri : |(b : ℝ)| * γ - |base| ≤ |base + (b : ℝ) * γ| := by
    have h := abs_sub_abs_le_abs_sub ((b : ℝ) * γ) (-base)
    rw [abs_neg, abs_mul, abs_of_pos hγ, sub_neg_eq_add, add_comm] at h
    exact h
  rw [Real.norm_eq_abs]
  linarith

/-- The `γ`-spaced norm-samples of a compact-support `φ` are summable (finite support). -/
lemma summable_norm_compactSupport_samples {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℂ}
    (hφ : HasCompactSupport φ) (base : ℝ) :
    Summable (fun k : ℤ => ‖φ (base - γ * (k : ℝ))‖) := by
  obtain ⟨u, hu⟩ := exists_finset_sample_support hγ hφ base
  refine summable_of_ne_finset_zero (s := u.image (Neg.neg)) (fun k hk => ?_)
  have hkn : (-k) ∉ u := fun h => hk (Finset.mem_image.mpr ⟨-k, h, neg_neg k⟩)
  rw [show base - γ * (k : ℝ) = base + ((-k : ℤ) : ℝ) * γ from by push_cast; ring,
    hu (-k) hkn, norm_zero]

/-- **Per-strip matching (gap g1 core).** A single strip's spatial γ-convolution
`∑'_j c_j·generalizedH1 τ(wbase+(j−ℓ)γ)` (with `c` finitely supported on `u`, the case
of a compact-support window sampled at γ-spacing) equals the finite-sum form
`∑_{b∈u} c_b·conj(P̂(b−ℓ))` consumed by `gamma_step34_vector`, where `P` is the
window `P`-object (`fourierCoeffOn P i = generalizedH1 τ(wbase+iγ)`).  Uses
`tsum_eq_sum` (finite support) and the realness `gaussianH1C_conj`.  This is the
exact bridge from `inner_periodization_p_strip_h1`'s spatial output to the ξ-side. -/
lemma strip_conv_match {γ : ℝ} (hγ : 0 < γ) (wbase : ℝ) (c : ℤ → ℂ) (u : Finset ℤ)
    (hu : ∀ b ∉ u, c b = 0) (P : ℝ → ℂ)
    (hP : ∀ i : ℤ, fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P i
        = (starRingEnd ℂ) (generalizedH1 τ (wbase + γ * (i : ℝ)))) (ℓ : ℤ) :
    (∑' j : ℤ, c j * generalizedH1 τ (wbase + γ * ((j - ℓ : ℤ) : ℝ)))
      = ∑ b ∈ u, c b * (starRingEnd ℂ)
          (fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P (b - ℓ)) := by
  have hrhs : ∀ b : ℤ, (starRingEnd ℂ)
      (fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P (b - ℓ))
        = generalizedH1 τ (wbase + γ * ((b - ℓ : ℤ) : ℝ)) := by
    intro b
    rw [hP (b - ℓ)]
    simp
  rw [tsum_eq_sum (s := u) fun b hb => by rw [hu b hb, zero_mul]]
  exact Finset.sum_congr rfl fun b _ => by rw [hrhs b]

/-- **Dense ξ-integral identity (per `t,s`) — gaps g1 assembled.** For a
compact-support window `φ`, the ℓ²-energy of the `p`-strip-coupled spatial
convolution (the integrand `A_{ℓ,t}(s)` of the regrouped LHS, with the strips
already summed) equals `γ` times the `ξ`-integral of the coupled product
`∑_r X_{φ,r}·conj(P_r)`, for suitable window `P`-objects `P_r` and finite sample
supports `u_r`.  This composes `strip_conv_match` (per strip, via the chosen
`exists_window_P` objects and `exists_finset_sample_support`) with the coupled
ξ-side Parseval `gamma_step34_vector`.  It is the complete dense ξ-side for a
fixed `(t,s)`; what remains is the Tonelli swap over `s` and the identification of
`∑_r X_r·conj(P_r)` with the project's matrix energy. -/
lemma dense_strip_energy_eq_xi_integral {α β : ℝ} {p q : ℕ}
    (hτ : 0 < τ.im) (hα : 0 < α) (hq : 0 < q)
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) (t : Fin q) (s : ℝ) :
    ∃ (Pr : Fin p → ℝ → ℂ) (u : Fin p → Finset ℤ),
      (∀ r : Fin p, MemLp (fun ξ => (starRingEnd ℂ) (Pr r ξ)) 2
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹))) ∧
      (∀ r : Fin p, ∀ i : ℤ,
        fourierCoeffOn (show (0 : ℝ) < (rationalZakGamma α q)⁻¹ from
            inv_pos.mpr (rationalZakGamma_pos hα hq)) (Pr r) i
          = (starRingEnd ℂ) (generalizedH1 τ
              ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
                + rationalZakGamma α q * (i : ℝ)))) ∧
      (∀ r : Fin p, ∀ b ∉ u r,
        φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * rationalZakGamma α q) = 0) ∧
      (Summable (fun ℓ : ℤ => ‖∑ r : Fin p, ∑' j : ℤ,
          (starRingEnd ℂ)
              (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q)) *
            generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
              + ((j - ℓ : ℤ) : ℝ) * rationalZakGamma α q)‖ ^ 2)) ∧
      (∑' ℓ : ℤ, ‖∑ r : Fin p, ∑' j : ℤ,
          (starRingEnd ℂ)
              (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q)) *
            generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
              + ((j - ℓ : ℤ) : ℝ) * rationalZakGamma α q)‖ ^ 2)
        = rationalZakGamma α q * ∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹,
            ‖∑ r : Fin p,
              (∑ b ∈ u r, (starRingEnd ℂ)
                  (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * rationalZakGamma α q)) *
                  Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
                    ((rationalZakGamma α q : ℂ) * (b : ℂ) * (ξ : ℂ)))) *
                (starRingEnd ℂ) (Pr r ξ)‖ ^ 2 := by
  set γ : ℝ := rationalZakGamma α q with hγdef
  have hγ : 0 < γ := rationalZakGamma_pos hα hq
  have hPex : ∀ r : Fin p, ∃ P : ℝ → ℂ,
      MemLp (fun ξ => (starRingEnd ℂ) (P ξ)) 2
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) γ⁻¹)) ∧
      ∀ i : ℤ, fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) P i
        = (starRingEnd ℂ) (generalizedH1 τ
            ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ)) + γ * (i : ℝ))) :=
    fun r => exists_window_P hτ hγ (s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
  obtain ⟨Pr, hPr⟩ := Classical.skolem.mp hPex
  have huex : ∀ r : Fin p, ∃ u : Finset ℤ,
      ∀ b ∉ u, φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ) = 0 :=
    fun r => exists_finset_sample_support hγ hφ (s - ((r : ℕ) : ℝ) * β⁻¹)
  obtain ⟨u, hu⟩ := Classical.skolem.mp huex
  have hstrip : ∀ (r : Fin p) (ℓ : ℤ),
      (∑' j : ℤ, (starRingEnd ℂ)
            (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * γ)) *
          generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
            + ((j - ℓ : ℤ) : ℝ) * γ))
        = ∑ b ∈ u r, (starRingEnd ℂ)
            (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ)) *
            (starRingEnd ℂ)
              (fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) (Pr r) (b - ℓ)) := by
    intro r ℓ
    have hcomm : (∑' j : ℤ, (starRingEnd ℂ)
            (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * γ)) *
          generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
            + ((j - ℓ : ℤ) : ℝ) * γ))
        = ∑' j : ℤ, (starRingEnd ℂ)
            (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * γ)) *
          generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
            + γ * ((j - ℓ : ℤ) : ℝ)) :=
      tsum_congr fun j => by rw [mul_comm ((j - ℓ : ℤ) : ℝ) γ]
    rw [hcomm]
    exact strip_conv_match hγ (s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
      (fun j => (starRingEnd ℂ) (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * γ)))
      (u r) (fun b hb => by rw [hu r b hb, map_zero]) (Pr r) (hPr r).2 ℓ
  refine ⟨Pr, u, fun r => (hPr r).1, fun r => (hPr r).2, hu, ?_, ?_⟩
  · exact ((summable_gamma_step34_vector hγ Finset.univ u
      (fun r b => (starRingEnd ℂ) (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ))) Pr
      (fun r _ => (hPr r).1)).congr (fun ℓ => congrArg (fun z : ℂ => ‖z‖ ^ 2)
        (Finset.sum_congr rfl (fun r _ => (hstrip r ℓ).symm))))
  calc (∑' ℓ : ℤ, ‖∑ r : Fin p, ∑' j : ℤ,
          (starRingEnd ℂ)
              (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * γ)) *
            generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
              + ((j - ℓ : ℤ) : ℝ) * γ)‖ ^ 2)
      = ∑' ℓ : ℤ, ‖∑ r : Fin p, ∑ b ∈ u r,
          (starRingEnd ℂ)
              (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ)) *
            (starRingEnd ℂ)
              (fourierCoeffOn (show (0 : ℝ) < γ⁻¹ from inv_pos.mpr hγ) (Pr r) (b - ℓ))‖ ^ 2 := by
        refine tsum_congr fun ℓ => ?_
        refine congrArg (fun z => ‖z‖ ^ 2) ?_
        exact Finset.sum_congr rfl fun r _ => hstrip r ℓ
    _ = γ * ∫ ξ in (0 : ℝ)..γ⁻¹,
          ‖∑ r : Fin p,
            (∑ b ∈ u r, (starRingEnd ℂ)
                (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ)) *
                Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
                  ((γ : ℂ) * (b : ℂ) * (ξ : ℂ)))) *
              (starRingEnd ℂ) (Pr r ξ)‖ ^ 2 :=
        gamma_step34_vector hγ Finset.univ u
          (fun r b => (starRingEnd ℂ) (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * γ)))
          Pr (fun r _ => (hPr r).1)

/-- Phase A: every `x ∈ L²(ℝ)` is approximated in norm by `Lp` elements with a
continuous, compactly supported representative. (Density half of obligation 3.) -/
lemma exists_continuous_compactSupport_Lp_approx
    (x : Lp ℂ 2 (volume : Measure ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      (∃ φ : ℝ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧
        (g : ℝ → ℂ) =ᵐ[volume] φ) ∧ ‖x - g‖ < ε := by
  obtain ⟨φ, hφ_cs, hφ_le, hφ_cont, hφ_mem⟩ :=
    (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp)
      (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  refine ⟨hφ_mem.toLp φ, ⟨φ, hφ_cont, hφ_cs, hφ_mem.coeFn_toLp⟩, ?_⟩
  have hcongr : eLpNorm (⇑(x - hφ_mem.toLp φ)) 2 volume = eLpNorm (⇑x - φ) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub x (hφ_mem.toLp φ), hφ_mem.coeFn_toLp] with t h1 h2
    rw [h1]; simp only [Pi.sub_apply, h2]
  rw [Lp.norm_def, hcongr]
  calc (eLpNorm (⇑x - φ) 2 volume).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hφ_le
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := by linarith

/-! ### B1, step 1 — the Gabor inner product as an explicit integral -/

/-- The Gabor coefficient `⟨x, M_{βn}T_{αm}h₁⟩` written as an explicit integral
against the conjugated window. First step of the modulation-Parseval bridge B1. -/
lemma inner_h1_element_eq_integral
    (α β : ℝ) (m n : ℤ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ x (generalizedH1ElementLp τ hτ α β m n) : ℂ) =
      ∫ t : ℝ, (starRingEnd ℂ) ((x : ℝ → ℂ) t) *
        generalizedH1Element τ α β m n t ∂(volume : Measure ℝ) := by
  rw [MeasureTheory.L2.inner_def]
  have hcoe : (generalizedH1ElementLp τ hτ α β m n : ℝ → ℂ) =ᵐ[volume]
      generalizedH1Element τ α β m n :=
    (memLp_generalizedH1Element hτ α β m n).coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with t ht
  rw [ht]
  exact RCLike.inner_apply' _ _

/-- The modulation factors out of the window: `h₁ₘₙ = e^{2πiβnv}·h₁ₘ₀`. -/
lemma h1_element_modulation_factor (α β : ℝ) (m n : ℤ) (v : ℝ) :
    generalizedH1Element τ α β m n v =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) * (v : ℂ)) *
        generalizedH1Element τ α β m 0 v := by
  simp only [generalizedH1Element, Int.cast_zero, mul_zero, zero_mul,
    Complex.exp_zero, one_mul]

/-- B1 link: the Gabor coefficient is a Fourier-transform sample of the windowed
function `wₘ(v) = conj(x v)·h₁ₘ₀(v)`, at frequency `-βn`. -/
lemma inner_h1_element_eq_fourier (α β : ℝ) (m n : ℤ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ x (generalizedH1ElementLp τ hτ α β m n) : ℂ) =
      𝓕 (fun v : ℝ => (starRingEnd ℂ) ((x : ℝ → ℂ) v) *
          generalizedH1Element τ α β m 0 v) (-(β * (n : ℝ))) := by
  rw [inner_h1_element_eq_integral, Real.fourier_real_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [h1_element_modulation_factor, Circle.smul_def, Real.fourierChar_apply]
  rw [show Complex.exp ((↑(2 * Real.pi * (-((v : ℝ) * (-(β * (n : ℝ)))))) : ℂ) * Complex.I) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) * (v : ℂ)) from by
    congr 1; push_cast; ring]
  ring

/-- The period-1 periodization of a continuous map lifts to a continuous map on
the circle. (Isolates the `F` construction for `modulation_parseval_beta`.) -/
lemma exists_periodizationCM (g : C(ℝ, ℂ)) :
    ∃ F : C(UnitAddCircle, ℂ), ⇑F = (g.periodic_tsum_comp_add_zsmul 1).lift :=
  ⟨⟨(g.periodic_tsum_comp_add_zsmul 1).lift,
      continuous_coinduced_dom.mpr (map_continuous _)⟩, rfl⟩

/-- Evaluation of the period-1 periodization at `↑u`: `lift(↑u) = ∑ₙ g(u+n)`. -/
lemma periodization_lift_coe (g : C(ℝ, ℂ))
    (hg_loc : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict (K : Set ℝ)‖)
    (u : ℝ) :
    (g.periodic_tsum_comp_add_zsmul 1).lift (u : UnitAddCircle) =
      ∑' n : ℤ, g (u + (n : ℝ)) := by
  rw [Function.Periodic.lift_coe]
  have hsum : Summable (fun n : ℤ => g.comp (ContinuousMap.addRight (n • (1 : ℝ)))) := by
    apply ContinuousMap.summable_of_locally_summable_norm
    intro K
    have := hg_loc K
    simpa [zsmul_eq_mul] using this
  rw [← ContinuousMap.tsum_apply hsum u]
  refine tsum_congr (fun n => ?_)
  simp [ContinuousMap.comp_apply, zsmul_eq_mul]

/-- The Fourier transform depends only on the a.e. class of the function. -/
lemma fourierIntegral_congr_ae {f g : ℝ → ℂ}
    (h : f =ᵐ[volume] g) (w : ℝ) : 𝓕 f w = 𝓕 g w := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards [h] with v hv
  rw [hv]

/-- Compact support is preserved under argument scaling `u ↦ u·η` (`η ≠ 0`). -/
lemma hasCompactSupport_comp_mul {f : ℝ → ℂ} (hf : HasCompactSupport f)
    {η : ℝ} (hη : η ≠ 0) :
    HasCompactSupport (fun u : ℝ => f (u * η)) := by
  have h := hf.comp_smul (c := η) hη
  simpa [smul_eq_mul, mul_comm] using h

/-- Dilation for the period integral: `∫_{(0,1]} f(u·η) = η⁻¹·∫_{(0,η]} f`. -/
lemma setIntegral_Ioc_dilation (f : ℝ → ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ u in Set.Ioc (0 : ℝ) 1, f (u * η)) = η⁻¹ * ∫ s in Set.Ioc (0 : ℝ) η, f s := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (le_of_lt hη),
    intervalIntegral.integral_comp_mul_right f (ne_of_gt hη)]
  simp [smul_eq_mul]

/-- Circle integral as an interval integral over one period `(0,1]`. -/
lemma circle_integral_norm_sq_eq_intervalIntegral (F : C(UnitAddCircle, ℂ)) :
    (∫ t : UnitAddCircle, ‖F t‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ a in Set.Ioc (0 : ℝ) 1, ‖F (a : UnitAddCircle)‖ ^ 2 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hvol : (AddCircle.haarAddCircle (T := 1)) = (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [hvol]
  have h := AddCircle.integral_preimage (1 : ℝ) (0 : ℝ) (fun t : AddCircle 1 => ‖F t‖ ^ 2)
  simp only [zero_add] at h
  rw [← h]

/-- The unmodulated window `h₁ₘ₀ = h1_element α β m 0` is continuous. -/
lemma continuous_h1_element_zero (α β : ℝ) (m : ℤ) :
    Continuous (fun v : ℝ => generalizedH1Element τ α β m 0 v) := by
  unfold generalizedH1Element generalizedH1
  continuity

/-- The windowed function `wₘ = conj(φ)·h₁ₘ₀` has compact support when `φ` does. -/
lemma hasCompactSupport_windowed (α β : ℝ) (m : ℤ) {φ : ℝ → ℂ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun v : ℝ =>
      (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v) := by
  have hconj : HasCompactSupport (fun v : ℝ => (starRingEnd ℂ) (φ v)) :=
    hφ.comp_left (g := starRingEnd ℂ) (by simp)
  exact hconj.mul_right

/-- **Per-`m` n-sum (B1 milestone), spatial form.** For `x` with continuous
compact-support representative `φ`, the modulation sum equals `η = β⁻¹` times the
`(0,η]`-integral of the squared spatial periodization `Aₘ(s) = ∑ₖ wₘ(s+kη)` — the
exact input to the student's ξ-side step (B3). -/
lemma gabor_nsum_eq_spatial (α β : ℝ) (hβ : 0 < β) (m : ℤ)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : C(ℝ, ℂ)) (hφ_cs : HasCompactSupport ⇑φ)
    (hxφ : (x : ℝ → ℂ) =ᵐ[volume] φ) :
    (∑' n : ℤ, ‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2) =
      β⁻¹ * ∫ s in Set.Ioc (0 : ℝ) β⁻¹,
        ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
          generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2 := by
  have hη : 0 < β⁻¹ := inv_pos.mpr hβ
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  let wm : C(ℝ, ℂ) :=
    ⟨fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v,
      (φ.continuous.star).mul (continuous_h1_element_zero α β m)⟩
  have hwm_coe : ⇑wm =
      fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v := rfl
  have hwm_cs : HasCompactSupport ⇑wm := hasCompactSupport_windowed α β m hφ_cs
  let g : C(ℝ, ℂ) := wm.comp ⟨fun u => u * β⁻¹, by fun_prop⟩
  have hg_fun : ⇑g = fun u => wm (u * β⁻¹) := rfl
  have hg_cs : HasCompactSupport ⇑g := by
    rw [hg_fun]; exact hasCompactSupport_comp_mul hwm_cs (ne_of_gt hη)
  have hg_loc := continuousMap_compactSupport_local_summable g hg_cs
  obtain ⟨F, hF⟩ := exists_periodizationCM g
  have hcirc : (∑' n : ℤ, ‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2) =
      (β⁻¹) ^ 2 * ∫ t : UnitAddCircle, ‖F t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    have hpar := modulation_parseval_beta wm hη g hg_fun hg_loc F hF
    rw [← hpar]
    have hterm : ∀ n : ℤ, ‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2 =
        ‖𝓕 (⇑wm) (-(β * (n : ℝ)))‖ ^ 2 := by
      intro n
      rw [inner_h1_element_eq_fourier]
      have hfeq : 𝓕 (fun v => (starRingEnd ℂ) ((x : ℝ → ℂ) v) *
            generalizedH1Element τ α β m 0 v) (-(β * (n : ℝ))) = 𝓕 (⇑wm) (-(β * (n : ℝ))) := by
        refine fourierIntegral_congr_ae ?_ _
        filter_upwards [hxφ] with v hv
        rw [hwm_coe, hv]
      rw [hfeq]
    rw [tsum_congr hterm]
    calc (∑' n : ℤ, ‖𝓕 (⇑wm) (-(β * (n : ℝ)))‖ ^ 2)
        = ∑' n : ℤ, ‖𝓕 (⇑wm) (((-n : ℤ) : ℝ) / β⁻¹)‖ ^ 2 := by
          refine tsum_congr (fun n => ?_)
          congr 3
          rw [Int.cast_neg, div_eq_mul_inv, inv_inv]; ring
      _ = ∑' n : ℤ, ‖𝓕 (⇑wm) ((n : ℝ) / β⁻¹)‖ ^ 2 :=
          Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => ‖𝓕 (⇑wm) ((n : ℝ) / β⁻¹)‖ ^ 2)
  have hFval : ∀ a : ℝ, ‖F (a : UnitAddCircle)‖ ^ 2 =
      (fun s => ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2) (a * β⁻¹) := by
    intro a
    have hsum : (∑' k : ℤ, g (a + (k : ℝ))) =
        ∑' k : ℤ, (starRingEnd ℂ) (φ (a * β⁻¹ + (k : ℝ) * β⁻¹)) *
          generalizedH1Element τ α β m 0 (a * β⁻¹ + (k : ℝ) * β⁻¹) := by
      refine tsum_congr (fun k => ?_)
      simp only [hg_fun, hwm_coe, add_mul]
    rw [hF, periodization_lift_coe g hg_loc a, hsum]
  have hieq : (∫ a in Set.Ioc (0 : ℝ) 1, ‖F (a : UnitAddCircle)‖ ^ 2) =
      ∫ a in Set.Ioc (0 : ℝ) 1,
        (fun s => ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
          generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2) (a * β⁻¹) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun a _ => hFval a)
  rw [hcirc, circle_integral_norm_sq_eq_intervalIntegral F, hieq,
    setIntegral_Ioc_dilation
      (fun s => ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2) hη,
    inv_inv, ← mul_assoc]
  congr 1
  field_simp

/-- **Per-`m` Gabor coefficient summability (compact-support class).** For `x` with a
continuous compact-support representative `φ`, the row sum `∑'_n ‖⟨x, g_{m,n}⟩‖²` is
summable — the analysis coefficients along one modulation channel are `ℓ²` (this is the
`L²`-circle Parseval finiteness, `summable_modulation_beta`, transported through the
`inner = Fourier sample` identity). This is exactly the per-`m` `n`-summability the
ENNReal `ofReal`/`tsum` interchange consumes. -/
lemma summable_gabor_nsum (α β : ℝ) (hβ : 0 < β) (m : ℤ)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : C(ℝ, ℂ)) (hφ_cs : HasCompactSupport ⇑φ)
    (hxφ : (x : ℝ → ℂ) =ᵐ[volume] φ) :
    Summable (fun n : ℤ => ‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2) := by
  have hη : 0 < β⁻¹ := inv_pos.mpr hβ
  let wm : C(ℝ, ℂ) :=
    ⟨fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v,
      (φ.continuous.star).mul (continuous_h1_element_zero α β m)⟩
  have hwm_coe : ⇑wm =
      fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v := rfl
  have hwm_cs : HasCompactSupport ⇑wm := hasCompactSupport_windowed α β m hφ_cs
  let g : C(ℝ, ℂ) := wm.comp ⟨fun u => u * β⁻¹, by fun_prop⟩
  have hg_fun : ⇑g = fun u => wm (u * β⁻¹) := rfl
  have hg_cs : HasCompactSupport ⇑g := by
    rw [hg_fun]; exact hasCompactSupport_comp_mul hwm_cs (ne_of_gt hη)
  have hg_loc := continuousMap_compactSupport_local_summable g hg_cs
  obtain ⟨F, hF⟩ := exists_periodizationCM g
  have hterm : ∀ n : ℤ, ‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2 =
      ‖𝓕 (⇑wm) (-(β * (n : ℝ)))‖ ^ 2 := by
    intro n
    rw [inner_h1_element_eq_fourier]
    have hfeq : 𝓕 (fun v => (starRingEnd ℂ) ((x : ℝ → ℂ) v) *
          generalizedH1Element τ α β m 0 v) (-(β * (n : ℝ))) = 𝓕 (⇑wm) (-(β * (n : ℝ))) := by
      refine fourierIntegral_congr_ae ?_ _
      filter_upwards [hxφ] with v hv
      rw [hwm_coe, hv]
    rw [hfeq]
  have hmodb := summable_modulation_beta wm hη g hg_fun hg_loc F hF
  have hneg : Summable (fun n : ℤ => ‖𝓕 (⇑wm) (((-n : ℤ) : ℝ) / β⁻¹)‖ ^ 2) :=
    (Equiv.neg ℤ).summable_iff.mpr hmodb
  refine hneg.congr (fun n => ?_)
  rw [hterm n, show ((-n : ℤ) : ℝ) / β⁻¹ = -(β * (n : ℝ)) from by
    rw [div_eq_mul_inv, inv_inv]; push_cast; ring]

/-- **Strip-amplitude `L²` regularity (compact-support class).** For continuous
compact-support `φ`, the strip amplitude `A_m(s) = ∑'_k conj φ(s+kβ⁻¹)·h₁(m,0)(s+kβ⁻¹)`
has integrable `‖·‖²` on the finite strip `(0,β⁻¹]`.  Reason: `A_m(s) = F((s·β)mod 1)`
for the continuous circle periodization `F`, so `A_m` is continuous, hence `‖A_m‖²` is
continuous and integrable on the bounded strip.  Consumed by the ENNReal
`ofReal ∫ = ∫⁻ ofReal` conversion. -/
lemma strip_amplitude_sq_integrableOn (α β : ℝ) (hβ : 0 < β) (m : ℤ)
    {φ : ℝ → ℂ} (hφ_cont : Continuous φ) (hφ_cs : HasCompactSupport φ) :
    IntegrableOn (fun s => ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2)
      (Set.Ioc (0 : ℝ) β⁻¹) volume := by
  have hη : 0 < β⁻¹ := inv_pos.mpr hβ
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  let φC : C(ℝ, ℂ) := ⟨φ, hφ_cont⟩
  let wm : C(ℝ, ℂ) :=
    ⟨fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v,
      (φC.continuous.star).mul (continuous_h1_element_zero α β m)⟩
  have hwm_coe : ⇑wm =
      fun v => (starRingEnd ℂ) (φ v) * generalizedH1Element τ α β m 0 v := rfl
  have hwm_cs : HasCompactSupport ⇑wm := hasCompactSupport_windowed α β m hφ_cs
  let g : C(ℝ, ℂ) := wm.comp ⟨fun u => u * β⁻¹, by fun_prop⟩
  have hg_fun : ⇑g = fun u => wm (u * β⁻¹) := rfl
  have hg_cs : HasCompactSupport ⇑g := by
    rw [hg_fun]; exact hasCompactSupport_comp_mul hwm_cs (ne_of_gt hη)
  have hg_loc := continuousMap_compactSupport_local_summable g hg_cs
  obtain ⟨F, hF⟩ := exists_periodizationCM g
  have hAeq : ∀ s : ℝ, (∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
      generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹))
      = F (((s * β : ℝ)) : UnitAddCircle) := by
    intro s
    rw [hF, periodization_lift_coe g hg_loc (s * β)]
    refine tsum_congr (fun k => ?_)
    have harg : (s * β + (k : ℝ)) * β⁻¹ = s + (k : ℝ) * β⁻¹ := by field_simp
    simp only [hg_fun, hwm_coe, harg]
  have hcont : Continuous (fun s : ℝ => ‖F (((s * β : ℝ)) : UnitAddCircle)‖ ^ 2) := by
    fun_prop
  exact ((hcont.integrableOn_Icc (a := 0) (b := β⁻¹)).mono_set
    Set.Ioc_subset_Icc_self).congr_fun
    (fun s _ => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hAeq s).symm) measurableSet_Ioc

/-- The unmodulated window is a shifted complex Gaussian:
`h1_element α β m 0 v = generalizedH1 τ (v − αm)`.  Bridges the LHS window to the
`generalizedH1 τ` samples that are the Fourier coefficients of the `P` matrix. -/
lemma h1_element_zero_eq_gaussianH1C (α β : ℝ) (m : ℤ) (v : ℝ) :
    generalizedH1Element τ α β m 0 v = generalizedH1 τ (v - α * (m : ℝ)) := by
  simp [generalizedH1Element]

/-- For a compactly supported `F`, the `p`-strip reindexed periodization family
`(r,j) ↦ F(s + (pj−r)β⁻¹)` is summable (it has finite support, since only finitely
many `k = pj−r` place `s+kβ⁻¹` in the compact support of `F`).  Discharges the
hypothesis of `periodization_p_strip_refine` on the dense compact-support class. -/
lemma summable_p_strip_of_compactSupport {p : ℕ} (hp : 0 < p) {β : ℝ} (hβ : 0 < β)
    {F : ℝ → ℂ} (hF : HasCompactSupport F) (s : ℝ) :
    Summable fun be : Fin p × ℤ =>
      (fun k : ℤ => F (s + (k : ℝ) * β⁻¹))
        ((p : ℤ) * be.2 - (((be.1 : Fin p) : ℕ) : ℤ)) := by
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ
  obtain ⟨R, _hR0, hR⟩ := hF.exists_pos_le_norm
  have hg : Summable (fun k : ℤ => F (s + (k : ℝ) * β⁻¹)) := by
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-(⌈(R + |s|) * β⌉₊ : ℤ)) (⌈(R + |s|) * β⌉₊ : ℤ)) ?_
    intro k hk
    apply hR (s + (k : ℝ) * β⁻¹)
    have hkInt : (⌈(R + |s|) * β⌉₊ : ℤ) + 1 ≤ |k| := by
      rw [Finset.mem_Icc] at hk
      rw [Int.abs_eq_natAbs]
      omega
    have hkabs : ((⌈(R + |s|) * β⌉₊ : ℝ)) + 1 ≤ |(k : ℝ)| := by
      have hcast : (((⌈(R + |s|) * β⌉₊ : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by
        exact_mod_cast hkInt
      rwa [Int.cast_abs, Int.cast_add, Int.cast_one, Int.cast_natCast] at hcast
    have hceil : (R + |s|) * β ≤ (⌈(R + |s|) * β⌉₊ : ℝ) := Nat.le_ceil _
    have hk2 : (R + |s|) * β ≤ |(k : ℝ)| := by linarith
    have hk3 : R + |s| ≤ |(k : ℝ)| * β⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hk2 (le_of_lt hβinv)
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hβ), mul_one] at h
    have htri : |(k : ℝ)| * β⁻¹ - |s| ≤ |s + (k : ℝ) * β⁻¹| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * β⁻¹) (-s)
      rw [abs_neg, abs_mul, abs_of_pos hβinv, sub_neg_eq_add, add_comm] at h
      exact h
    rw [Real.norm_eq_abs]
    linarith
  let e : Fin p × ℤ ≃ ℤ := (Equiv.prodComm (Fin p) ℤ).trans (intQMulSubFinEquiv p hp)
  have hcomp : (fun be : Fin p × ℤ =>
      (fun k : ℤ => F (s + (k : ℝ) * β⁻¹))
        ((p : ℤ) * be.2 - (((be.1 : Fin p) : ℕ) : ℤ)))
      = (fun k : ℤ => F (s + (k : ℝ) * β⁻¹)) ∘ e := by
    funext be; rfl
  rw [hcomp]
  exact (Equiv.summable_iff e).mpr hg

/-- **Dense-calc step 4 (per-strip refinement, h₁ window).** The inner
η-periodization in the LHS regrouped energy splits, via `k = pj−r`, into `p`
γ-spaced strips, each a γ-convolution of `conj φ` with a `generalizedH1 τ` sample at
strip base `s−rβ⁻¹+αt`.  This is the exact spatial input to the ξ-side step
(B3 / `gamma_step34`). -/
lemma inner_periodization_p_strip_h1 {α β : ℝ} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hβ : 0 < β) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) (t : Fin q) (ℓ : ℤ) (s : ℝ) :
    (∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0
          (s + (k : ℝ) * β⁻¹)) =
      ∑ r : Fin p, ∑' j : ℤ,
        (starRingEnd ℂ)
            (φ ((s - (((r : Fin p) : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q)) *
          generalizedH1 τ ((s - (((r : Fin p) : ℕ) : ℝ) * β⁻¹ + α * (((t : Fin q) : ℕ) : ℝ))
            + ((j - ℓ : ℤ) : ℝ) * rationalZakGamma α q) := by
  have hFcs : HasCompactSupport (fun u : ℝ => (starRingEnd ℂ) (φ u) *
      generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0 u) := by
    have hconj : HasCompactSupport (fun u : ℝ => (starRingEnd ℂ) (φ u)) :=
      hφ.comp_left (g := starRingEnd ℂ) (by simp)
    exact hconj.mul_right
  have hsum := summable_p_strip_of_compactSupport hp hβ hFcs s
  have key := periodization_p_strip_refine hp hq hβ hαβ
      (fun u : ℝ => (starRingEnd ℂ) (φ u) *
        generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0 u) s hsum
  refine key.trans ?_
  refine Finset.sum_congr rfl fun r _ => tsum_congr fun j => ?_
  show (starRingEnd ℂ) (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q)) *
      generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0
        ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q) = _
  rw [h1_element_zero_eq_gaussianH1C, p_strip_h1_arg t (s - ((r : ℕ) : ℝ) * β⁻¹) j ℓ]

/-- The shifted honest fiber `v_x` vanishes off the fundamental rectangle. -/
lemma rationalPositiveFiberField_eq_zero_of_not_mem
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∉ rationalPositiveFundamentalRect α p q) :
    rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z = 0 := by
  funext r
  unfold rationalPositiveFiberField rationalPositiveSpecFiberField
  rw [if_neg hz]
  rfl

/-- Abbreviation for the right-hand side as a function of `x`. -/
noncomputable def gammaMatrixEnergyIntegral
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) → ℝ :=
  fun x => ∫ z, generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z
    ∂(volume : Measure (ℝ × ℝ))

/-- Pointwise RHS bound: given a uniform matrix upper bound `B`, the gamma
matrix energy is dominated by `ηγB` times the component energy of `v_x`. -/
lemma gammaMatrixEnergy_le_of_matrix_bound
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z w, ‖generalizedRationalZakMatrix τ α p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (z : ℝ × ℝ) :
    generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z ≤
      rationalZakEta α p q * rationalZakGamma α q * B *
        ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  have hη : 0 ≤ rationalZakEta α p q := le_of_lt (rationalZakEta_pos hα hβ hgap hαβ)
  have hγ : 0 ≤ rationalZakGamma α q :=
    le_of_lt (rationalZakGamma_pos hα (q_pos_of_gap hgap))
  set v := rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z with hv
  set D := rationalPositiveFourierRowChange α p q z with hD
  -- matrix applied to the gamma fiber
  have hmv : generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z =
      (p : ℂ)⁻¹ • (generalizedRationalZakMatrix τ α p q z *ᵥ (Dᴴ *ᵥ v)) := by
    unfold rationalPositiveGammaFiberField
    rw [Matrix.mulVec_smul]
  have hnorm : ‖generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 =
      ((p : ℝ)⁻¹) ^ 2 * ‖generalizedRationalZakMatrix τ α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2 := by
    rw [hmv, norm_smul, mul_pow]
    congr 2
    rw [norm_inv, Complex.norm_natCast]
  have hrow : ‖Dᴴ *ᵥ v‖ ^ 2 ≤ (p : ℝ) ^ 2 * ‖v‖ ^ 2 :=
    rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_sq_le α p q z v
  have hmatrix : ‖generalizedRationalZakMatrix τ α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2 ≤ B * ‖Dᴴ *ᵥ v‖ ^ 2 :=
    hB z (Dᴴ *ᵥ v)
  have hkey : ‖generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 ≤
      B * ‖v‖ ^ 2 := by
    rw [hnorm]
    calc ((p : ℝ)⁻¹) ^ 2 * ‖generalizedRationalZakMatrix τ α p q z *ᵥ (Dᴴ *ᵥ v)‖ ^ 2
        ≤ ((p : ℝ)⁻¹) ^ 2 * (B * ‖Dᴴ *ᵥ v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmatrix (by positivity)
      _ ≤ ((p : ℝ)⁻¹) ^ 2 * (B * ((p : ℝ) ^ 2 * ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrow hB0) (by positivity)
      _ = B * ‖v‖ ^ 2 := by field_simp
  have hvsum : ‖v‖ ^ 2 ≤ ∑ r : Fin p, ‖v r‖ ^ 2 := pi_norm_sq_le_sum_norm_sq v
  unfold generalizedRationalPositiveGammaMatrixEnergy
  calc rationalZakEta α p q * rationalZakGamma α q *
        ‖generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
      ≤ rationalZakEta α p q * rationalZakGamma α q * (B * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg hη hγ)
    _ ≤ rationalZakEta α p q * rationalZakGamma α q * (B * ∑ r : Fin p, ‖v r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hvsum hB0) (mul_nonneg hη hγ)
    _ = rationalZakEta α p q * rationalZakGamma α q * B * ∑ r : Fin p, ‖v r‖ ^ 2 := by ring

/-- RHS Bessel bound: given a uniform matrix upper bound `B`, the matrix-energy
integral is bounded by `γ B ‖x‖²`. Axiom-clean (takes `B` as a hypothesis);
this is the key estimate feeding LHS continuity (Phase C2). -/
lemma gammaMatrixEnergyIntegral_le_of_matrix_bound
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z w, ‖generalizedRationalZakMatrix τ α p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    gammaMatrixEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x ≤
      rationalZakGamma α q * B * ‖x‖ ^ 2 := by
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hγ : 0 ≤ rationalZakGamma α q :=
    le_of_lt (rationalZakGamma_pos hα (q_pos_of_gap hgap))
  set c : ℝ := rationalZakEta α p q * rationalZakGamma α q * B with hc
  have hcomp_int :=
    rationalPositiveFiberField_component_energy_integrable hα hβ hpq_coprime hgap hαβ x
  have hg_int : Integrable
      (fun z : ℝ × ℝ => c *
        ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := hcomp_int.const_mul c
  have h0 : 0 ≤ᵐ[(volume : Measure (ℝ × ℝ))]
      fun z => generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z := by
    filter_upwards with z
    unfold generalizedRationalPositiveGammaMatrixEnergy
    have : 0 ≤ rationalZakEta α p q * rationalZakGamma α q :=
      mul_nonneg (le_of_lt hη) hγ
    positivity
  have hle : (fun z => generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z)
      ≤ᵐ[(volume : Measure (ℝ × ℝ))]
      fun z => c *
        ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := by
    filter_upwards with z
    have := gammaMatrixEnergy_le_of_matrix_bound hα hβ hpq_coprime hgap hαβ hB0 hB x z
    simpa [hc, mul_assoc] using this
  have hmono := MeasureTheory.integral_mono_of_nonneg h0 hg_int hle
  rw [MeasureTheory.integral_const_mul,
    rationalPositiveFiberField_component_energy_identity_scaled
      hα hβ hpq_coprime hgap hαβ x] at hmono
  -- hmono : gammaMatrixEnergyIntegral x ≤ c * ((η)⁻¹ * ‖x‖²)
  have hfinal : c * ((rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2) =
      rationalZakGamma α q * B * ‖x‖ ^ 2 := by
    have hηne : rationalZakEta α p q ≠ 0 := ne_of_gt hη
    rw [hc, show rationalZakEta α p q * rationalZakGamma α q * B *
          ((rationalZakEta α p q)⁻¹ * ‖x‖ ^ 2) =
        (rationalZakEta α p q * (rationalZakEta α p q)⁻¹) *
          (rationalZakGamma α q * B * ‖x‖ ^ 2) from by ring,
      mul_inv_cancel₀ hηne, one_mul]
  rw [hfinal] at hmono
  exact hmono

/-- Continuity of the generalized rational-Zak window matrix, obtained from
the verified modular theta formula. -/
lemma continuous_rationalZakPMatrixH1_gaussian {α : ℝ} {p q : ℕ}
    (hτ : 0 < τ.im) (hγ : 0 < rationalZakGamma α q) :
    Continuous (generalizedRationalZakPMatrix τ α p q) := by
  apply continuous_matrix
  intro s t
  have hbase := continuous_generalizedZakH1ModularClosedForm
    (ne_of_gt hγ) hτ
  have hmap : Continuous fun z : ℝ × ℝ =>
      (z.1 + α * ((t : ℕ) : ℝ) +
        rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ), z.2) := by
    continuity
  have hcomp := hbase.comp hmap
  apply hcomp.congr
  intro z
  unfold generalizedRationalZakPMatrix
  exact (generalizedZakH1_modular_formula (ne_of_gt hγ) hτ _ _).symm

/-- **The uniform matrix upper bound `B`, axiom-clean.** Continuity of the window
matrix gives uniformly bounded entries (via the two norm-periodicities), hence the
operator bound `‖generalizedRationalZakMatrix τ z *ᵥ w‖² ≤ B‖w‖²` consumed by
`gammaMatrixEnergyIntegral_le_of_matrix_bound` / `gammaMatrixEnergy_le_of_matrix_bound`.
This discharges the matrix-bound hypothesis of the continuity obligations *without*
the FrobeniusDeterminant cyclic-minor axiom or any Gaussian closed-form *axiom* — the closed form is
now a proved theorem. -/
lemma rationalZakMatrix_uniform_bound_gaussian {α : ℝ} {p q : ℕ}
    (hτ : 0 < τ.im) (hγ : 0 < rationalZakGamma α q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z w, ‖generalizedRationalZakMatrix τ α p q z *ᵥ w‖ ^ 2 ≤ B * ‖w‖ ^ 2 := by
  classical
  have hcont : Continuous (generalizedRationalZakPMatrix τ α p q) :=
    continuous_rationalZakPMatrixH1_gaussian hτ hγ
  have hPbd : ∀ i j, ∃ Cij : ℝ, ∀ z,
      ‖generalizedRationalZakPMatrix τ α p q z i j‖ ≤ Cij := by
    intro i j
    have hc : Continuous fun z : ℝ × ℝ =>
        generalizedRationalZakPMatrix τ α p q z i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hcont)
    apply exists_norm_bound_of_continuous_norm_periodic_prod hγ (inv_pos.mpr hγ) hc
    · intro z
      unfold generalizedRationalZakPMatrix
      let y : ℝ := z.1 + α * ((j : ℕ) : ℝ) +
        rationalZakGamma α q * ((i : ℕ) : ℝ) / (p : ℝ)
      have hy :
          (z.1 + rationalZakGamma α q) + α * ((j : ℕ) : ℝ) +
              rationalZakGamma α q * ((i : ℕ) : ℝ) / (p : ℝ) =
            y + rationalZakGamma α q := by
        dsimp [y]
        ring
      rw [hy, Zak.zakTransform_add_period, norm_mul]
      have hphase :
          ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (rationalZakGamma α q : ℂ) * (z.2 : ℂ))‖ = 1 := by
        have harg :
            2 * (Real.pi : ℂ) * Complex.I *
                (rationalZakGamma α q : ℂ) * (z.2 : ℂ) =
              ((2 * Real.pi * rationalZakGamma α q * z.2 : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hphase, one_mul]
    · intro z
      unfold generalizedRationalZakPMatrix
      exact congrArg norm (Zak.zakTransform_freq_period (ne_of_gt hγ)
        (generalizedH1 τ) _ _)
  have hMbd := conjTranspose_matrix_field_entries_bounded
    hPbd
  choose Cij hCij using hMbd
  refine rationalZakMatrix_uniform_upper_bound_of_entry_bound (generalizedRationalZakMatrix τ α p q)
    (C := ∑ i : Fin q, ∑ j : Fin p, |Cij i j|)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))
    (fun z i j => ?_)
  calc ‖generalizedRationalZakMatrix τ α p q z i j‖
      ≤ Cij i j := hCij i j z
    _ ≤ |Cij i j| := le_abs_self _
    _ ≤ ∑ j' : Fin p, |Cij i j'| :=
        Finset.single_le_sum (f := fun j' : Fin p => |Cij i j'|)
          (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin q, ∑ j' : Fin p, |Cij i' j'| :=
        Finset.single_le_sum (f := fun i' : Fin q => ∑ j' : Fin p, |Cij i' j'|)
          (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _)) (Finset.mem_univ i)

/-- **Unconditional RHS Bessel bound (axiom-clean).** Combining the axiom-clean
matrix bound with `gammaMatrixEnergyIntegral_le_of_matrix_bound`: the matrix-energy
integral is `≤ γB‖x‖²` for *all* `x`, with a fixed `B`.  This is the upper estimate
that drives the Fatou step for LHS continuity (obligation 1), now free of any axiom. -/
lemma gammaMatrixEnergyIntegral_le {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      gammaMatrixEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x
        ≤ rationalZakGamma α q * B * ‖x‖ ^ 2 := by
  obtain ⟨B, hB0, hB⟩ :=
    rationalZakMatrix_uniform_bound_gaussian hτ
      (rationalZakGamma_pos hα (q_pos_of_gap hgap))
  exact ⟨B, hB0, fun x =>
    gammaMatrixEnergyIntegral_le_of_matrix_bound hα hβ hpq_coprime hgap hαβ hB0 hB x⟩

/-- **Lower semicontinuity of the coefficient energy (Fatou ingredient).** As an
`ℝ≥0∞`-valued sum of continuous (hence lower-semicontinuous) terms `x ↦ ‖⟨x,g_{mn}⟩‖²`,
the coefficient energy is lower semicontinuous.  This is the Fatou half of the
upper-Bessel bound: combined with the dense identity and the unconditional RHS bound
`gammaMatrixEnergyIntegral_le`, it gives `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) x ≤ γB‖x‖²` for all `x`
(obligation 1 then follows, *without* needing obligation 2). -/
lemma productCoeffEnergy_ennreal_lowerSemicontinuous (α β : ℝ) :
    LowerSemicontinuous (fun x : Lp ℂ 2 (volume : Measure ℝ) =>
      ∑' mn : ℤ × ℤ,
        ENNReal.ofReal (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2)) := by
  apply lowerSemicontinuous_tsum
  intro mn
  apply Continuous.lowerSemicontinuous
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

/-- **Shift into a subinterval preserves `MemLp`.** If `f ∈ L²((0,T])` and
`[c, c+S] ⊆ [0,T]`, then `ξ ↦ f(ξ+c) ∈ L²((0,S])` (measure-preserving translation
onto the subinterval).  Used to see each `a`-shifted base fiber is `L²` on `(0,γ⁻¹]`. -/
lemma memLp_shift_subinterval {T c S : ℝ} (hc : 0 ≤ c) (hS : c + S ≤ T) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    MemLp (fun ξ => f (ξ + c)) 2 (volume.restrict (Set.Ioc (0 : ℝ) S)) := by
  have hpre : (fun ξ : ℝ => ξ + c) ⁻¹' (Set.Ioc c (c + S)) = Set.Ioc (0 : ℝ) S := by
    ext ξ; simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmpr : MeasurePreserving (fun ξ : ℝ => ξ + c)
      (volume.restrict (Set.Ioc (0 : ℝ) S)) (volume.restrict (Set.Ioc c (c + S))) := by
    have := (measurePreserving_add_right (volume : Measure ℝ) c).restrict_preimage
      (measurableSet_Ioc : MeasurableSet (Set.Ioc c (c + S)))
    rwa [hpre] at this
  exact (hf.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc hc hS) le_rfl)).comp_measurePreserving
    hmpr

/-- **Pointwise fiberization (B4 step 1).** Inside the fundamental rectangle the
gamma fiber `X_x = p⁻¹ Dᴴ v_x` is the explicit finite sum over the honest base
fiber shifted by `a/γ`, weighted by the conjugated row-change phase
`exp(2πi(r·η·ξ + a·r/p))`. -/
lemma gammaFiberField_apply_eq_sum {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∈ rationalPositiveFundamentalRect α p q) (r : Fin p)
    (hslice : ∀ a : Fin p,
      rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
      rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x z.1
        (z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z r
      = (p : ℂ)⁻¹ * ∑ a : Fin p,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (z.2 : ℂ)
              + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))
          * rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x z.1
              (z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q) := by
  rw [rationalPositiveGammaFiberField, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show ((rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ
        rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z) r
      = ∑ a : Fin p, (rationalPositiveFourierRowChange α p q z)ᴴ r a *
          rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z a
      from by simp [Matrix.mulVec, dotProduct]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rationalPositiveFiberField_eq_base_of_mem_rect hα hβ hpq_coprime hgap hαβ x hz a,
    Matrix.conjTranspose_apply]
  rw [hslice a]
  congr 1
  simp only [rationalPositiveFourierRowChange]
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_add, map_div₀, Complex.conj_I, Complex.conj_ofReal,
    map_natCast, map_ofNat]
  ring

/-- **Fiber-component `MemLp` on the frequency period.** For `s ∈ (0,η]`, the map
`ξ ↦ X_{x,r}(s,ξ)` is `L²((0,γ⁻¹])` — it equals a finite sum of unimodular-phase-
weighted shifted base fibers (`gammaFiberField_apply_eq_sum`), each `L²` by
`memLp_shift_subinterval`.  Supplies the `MemLp` side of the `gf =ᵐ zakTransform`
uniqueness step. -/
lemma gammaFiberField_component_memLp {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q)) (r : Fin p)
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    MemLp (fun ξ => rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ) r) 2
      (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)) := by
  have hγ0 : 0 < rationalZakGamma α q := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  have hηeq : (rationalZakEta α p q)⁻¹ = (p : ℝ) / rationalZakGamma α q :=
    rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ
  have hbase := rationalPositiveBaseFrequencyFiber_memLp hα hβ hgap hαβ x s
  have hsum : MemLp (fun ξ : ℝ => (p : ℂ)⁻¹ * ∑ a : Fin p,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
            + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))
        * rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)) := by
    refine MemLp.const_mul ?_ _
    refine memLp_finset_sum _ (fun a _ => ?_)
    have hshift : MemLp (fun ξ : ℝ => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
        (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) 2
        (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)) := by
      refine memLp_shift_subinterval (by positivity) ?_ _ hbase
      rw [hηeq, inv_eq_one_div, ← add_div]
      gcongr
      exact_mod_cast Nat.succ_le_of_lt a.isLt
    have hmeas : AEStronglyMeasurable (fun ξ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
            + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))
        * rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q))
        (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)) :=
      (Continuous.aestronglyMeasurable (by fun_prop)).mul hshift.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine ((memLp_two_iff_integrable_sq_norm hshift.aestronglyMeasurable).mp hshift).congr ?_
    filter_upwards with ξ
    have hn1 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
          + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))‖ = 1 := by
      have harg : 2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
            + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ))
          = ((2 * Real.pi * (((r : ℕ) : ℝ) * rationalZakEta α p q * ξ
              + ((a : ℕ) : ℝ) * ((r : ℕ) : ℝ) / (p : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg]; exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hn1, one_mul]
  refine hsum.ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hslice] with ξ hξ hsliceξ
  exact (gammaFiberField_apply_eq_sum hα hβ hpq_coprime hgap hαβ x
    (show ((s, ξ) : ℝ × ℝ) ∈ rationalPositiveFundamentalRect α p q from ⟨hs, hξ⟩)
    r hsliceξ).symm

/-- **`p`-piece tiling (B4 step 2 core).** The `p` shifted integrals over the
`γ`-period `(0, γ⁻¹]` (shifts `a/γ`, `a = 0,…,p−1`) reassemble into a single
integral over the full `η`-period `(0, p/γ] = (0, η⁻¹]`. This is the measure-
theoretic heart of the Zibulski–Zeevi fiberization: `∑_a (a-piece) = full period`. -/
lemma tiling_sum_integral {γ : ℝ} (hγ : 0 < γ) (p : ℕ) (F : ℝ → ℂ)
    (hint : ∀ k : ℕ, k < p → IntervalIntegrable F volume ((k : ℝ) / γ) (((k : ℝ) + 1) / γ)) :
    ∑ a : Fin p, (∫ ξ in (0 : ℝ)..γ⁻¹, F (ξ + ((a : ℕ) : ℝ) / γ))
      = ∫ ξ in (0 : ℝ)..((p : ℝ) / γ), F ξ := by
  have hstep : ∀ a : Fin p, (∫ ξ in (0 : ℝ)..γ⁻¹, F (ξ + ((a : ℕ) : ℝ) / γ))
      = ∫ ξ in ((a : ℕ) : ℝ) / γ..(((a : ℕ) : ℝ) + 1) / γ, F ξ := by
    intro a
    rw [intervalIntegral.integral_comp_add_right F (((a : ℕ) : ℝ) / γ)]
    congr 1
    · exact zero_add _
    · rw [inv_eq_one_div, ← add_div, add_comm]
  rw [Finset.sum_congr rfl (fun a _ => hstep a),
    Fin.sum_univ_eq_sum_range (fun k => ∫ ξ in (k : ℝ) / γ..((k : ℝ) + 1) / γ, F ξ) p]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F)
    (a := fun k : ℕ => (k : ℝ) / γ) (n := p)
    (fun k hk => by push_cast; exact hint k hk)
  simp only [Nat.cast_add, Nat.cast_one] at hadj
  rw [hadj]
  simp

/-- **Fiberization phase cancellation (B4 step 2).** The `fourierCoeffOn` mode
`exp(-2πikγξ)` times the row-change phase equals the pure mode
`exp(2πi(rη−kγ)(ξ+a/γ))` in the *shifted* variable — the two `exp(±2πi ar/p)`
factors cancel (using `η = γ/p`) up to the integer `exp(−2πi ka) = 1`. This is
what lets the shifted base-fiber integrals reassemble via `tiling_sum_integral`. -/
lemma fiberization_phase_eq {α : ℝ} {p q : ℕ} (hp : 0 < p) (hα : 0 < α) (hq : 0 < q)
    (r : Fin p) (k : ℤ) (a : Fin p) (ξ : ℝ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (k : ℂ) * (rationalZakGamma α q : ℂ) * (ξ : ℂ))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
            + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
            * ((ξ : ℂ) + ((a : ℕ) : ℂ) / (rationalZakGamma α q : ℂ))) := by
  have hγ0 : (rationalZakGamma α q : ℝ) ≠ 0 := ne_of_gt (rationalZakGamma_pos hα hq)
  have hγℂ : (rationalZakGamma α q : ℂ) ≠ 0 := by exact_mod_cast hγ0
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hη : (rationalZakEta α p q : ℂ) = (rationalZakGamma α q : ℂ) / (p : ℂ) := by
    rw [rationalZakEta]; push_cast; ring
  rw [show (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
            * ((ξ : ℂ) + ((a : ℕ) : ℂ) / (rationalZakGamma α q : ℂ)))
      = (-(2 * (Real.pi : ℂ)) * Complex.I * (k : ℂ) * (rationalZakGamma α q : ℂ) * (ξ : ℂ)
          + 2 * (Real.pi : ℂ) * Complex.I *
            (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (ξ : ℂ)
              + ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))
        + ((-(k * ((a : ℕ) : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by
      rw [hη]; field_simp; push_cast; ring]
  simp only [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Modulated gamma fiber as a shifted-base-fiber sum (B4 step 2).** Multiplying
the gamma fiber by the `fourierCoeffOn` mode `exp(-2πikγξ)` and applying the
phase cancellation turns it into `p⁻¹ ∑_a H(ξ+a/γ)` with the pure-mode base fiber
`H(ξ') = exp(2πi(rη−kγ)ξ')·baseFiber(ξ')`, whose `a`-shifted pieces tile. -/
lemma gammaFiberField_mode_eq_sum {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∈ rationalPositiveFundamentalRect α p q) (r : Fin p) (k : ℤ)
    (hslice : ∀ a : Fin p,
      rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
        (z.1, z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
      rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x z.1
        (z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (k : ℂ) * (rationalZakGamma α q : ℂ) * (z.2 : ℂ))
        * rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z r
      = (p : ℂ)⁻¹ * ∑ a : Fin p,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
              * ((z.2 : ℂ) + ((a : ℕ) : ℂ) / (rationalZakGamma α q : ℂ)))
          * rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x z.1
              (z.2 + ((a : ℕ) : ℝ) / rationalZakGamma α q) := by
  rw [gammaFiberField_apply_eq_sum hα hβ hpq_coprime hgap hαβ x hz r hslice, mul_left_comm,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← mul_assoc,
    fiberization_phase_eq (p_pos_of_density hα hβ hgap hαβ) hα (q_pos_of_gap hgap) r k a z.2]

/-- **Base-fiber pure-mode integral (B4 step 2).** The integral of the pure mode
`exp(2πi(rη−kγ)ξ')` against the honest base fiber over its full period `(0,η⁻¹]`
is `η⁻¹` times the window sample `x(s+ηr−γk)`, via the `AddCircle` character
bridge and the base-fiber Fourier-coefficient formula (index `pk−r`). -/
lemma baseFiber_mode_integral {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) (r : Fin p) (k : ℤ)
    (hc : Summable (fun m : ℤ =>
        ‖(fun t : ℝ => (x : ℝ → ℂ) t) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2)) :
    (∫ ξ' in (0 : ℝ)..(rationalZakEta α p q)⁻¹,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
            * (ξ' : ℂ))
        • rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ξ')
      = (rationalZakEta α p q)⁻¹ •
          (fun t : ℝ => (x : ℝ → ℂ) t)
            (s - rationalZakEta α p q * (((p : ℤ) * k - (r : ℕ) : ℤ) : ℝ)) := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hη0 : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hηinv : (0 : ℝ) < (rationalZakEta α p q)⁻¹ := inv_pos.mpr hη0
  have hγη : (rationalZakGamma α q : ℂ) = (p : ℂ) * (rationalZakEta α p q : ℂ) := by
    rw [rationalZakEta]; push_cast; field_simp
  have hexp : ∀ ξ' : ℝ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
          * (ξ' : ℂ))
      = (fourier (((r : ℕ) : ℤ) - (p : ℤ) * k)) (↑ξ' : AddCircle (rationalZakEta α p q)⁻¹) := by
    intro ξ'
    rw [← zakPhase_eq_fourier_coe hη0 (((r : ℕ) : ℤ) - (p : ℤ) * k) ξ']
    congr 1
    rw [hγη]; push_cast; ring
  simp_rw [hexp]
  have hfi := fourierCoeffOn_eq_integral
    (fun ξ' => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ξ')
    ((p : ℤ) * k - (r : ℕ)) hηinv
  rw [rationalPositiveBaseFrequencyFiber_fourierCoeffOn hα hβ hgap hαβ x s hc
      ((p : ℤ) * k - (r : ℕ))] at hfi
  rw [show (rationalZakEta α p q)⁻¹ - (0 : ℝ) = (rationalZakEta α p q)⁻¹ from sub_zero _] at hfi
  simp only [neg_sub, one_div, inv_inv] at hfi
  rw [hfi, smul_smul, inv_mul_cancel₀ (ne_of_gt hη0), one_smul]

/-- **Base-fiber interval integrability (B4 step 2 plumbing).** The honest base
fiber is `L²` on its period `(0, η⁻¹]`, hence interval-integrable on any
`[a, b] ⊆ [0, η⁻¹]` — supplies the `IntervalIntegrable` hypotheses of
`tiling_sum_integral` and `integral_finset_sum`. -/
lemma baseFiber_intervalIntegrable {α β : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (rationalZakEta α p q)⁻¹) :
    IntervalIntegrable (fun ω => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω)
      volume a b := by
  have hint : IntegrableOn (fun ω => rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ω)
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q)⁻¹) volume :=
    (rationalPositiveBaseFrequencyFiber_memLp hα hβ hgap hαβ x s).integrable (by norm_num)
  constructor
  · exact hint.mono_set (Set.Ioc_subset_Ioc ha hb)
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]; exact integrableOn_empty

/-- **B4 STEP 2 CAPSTONE — the gamma fiber is φ's γ-Zak.** For a base point
`s ∈ (0, η]`, the `k`-th interval Fourier coefficient of `ξ ↦ X_{x,r}(s,ξ)` is the
window sample `x(s − η(pk−r)) = x(s + ηr − γk)`. So `X_{x,r}(s,·)` is exactly the
`γ`-Zak fiber of `x` at base `s + ηr` — the Zibulski–Zeevi fiberization identity. -/
lemma gammaFiberField_fourierCoeffOn {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q)) (r : Fin p) (k : ℤ)
    (hc : Summable (fun m : ℤ =>
        ‖(fun t : ℝ => (x : ℝ → ℂ) t) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    fourierCoeffOn (show (0 : ℝ) < (rationalZakGamma α q)⁻¹ from
        inv_pos.mpr (rationalZakGamma_pos hα (q_pos_of_gap hgap)))
        (fun ξ => rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ) r) k
      = (fun t : ℝ => (x : ℝ → ℂ) t)
          (s - rationalZakEta α p q * (((p : ℤ) * k - (r : ℕ) : ℤ) : ℝ)) := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hη0 : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hγ0 : 0 < rationalZakGamma α q := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  have hγℂ : (rationalZakGamma α q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hγ0
  have hηℂ : (rationalZakEta α p q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη0
  have hγη : (rationalZakGamma α q : ℂ) = (p : ℂ) * (rationalZakEta α p q : ℂ) := by
    rw [rationalZakEta]; push_cast; field_simp
  have hηeq : (rationalZakEta α p q)⁻¹ = (p : ℝ) / rationalZakGamma α q :=
    rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ
  set H : ℝ → ℂ := fun ξ' => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) - (k : ℂ) * (rationalZakGamma α q : ℂ))
        * (ξ' : ℂ))
    • rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s ξ' with hHdef
  -- H is interval-integrable on each of the first p γ-pieces (⊆ (0, η⁻¹])
  have hHint : ∀ m : ℕ, m < p → IntervalIntegrable H volume ((m : ℝ) / rationalZakGamma α q)
      (((m : ℝ) + 1) / rationalZakGamma α q) := by
    intro m hm
    have hbf := baseFiber_intervalIntegrable hα hβ hgap hαβ x s
      (a := (m : ℝ) / rationalZakGamma α q) (b := ((m : ℝ) + 1) / rationalZakGamma α q)
      (by positivity) (by gcongr; linarith)
      (by rw [hηeq]; gcongr; exact_mod_cast hm)
    exact hbf.continuousOn_mul (by fun_prop : Continuous (fun ξ' : ℝ => Complex.exp _)).continuousOn
  -- each a-shifted piece is interval-integrable on (0, γ⁻¹]
  have hHshift : ∀ a : Fin p, IntervalIntegrable (fun ξ => H (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q))
      volume 0 (rationalZakGamma α q)⁻¹ := by
    intro a
    have := (hHint (a : ℕ) a.isLt).comp_add_right (((a : ℕ) : ℝ) / rationalZakGamma α q)
    have hlo : (↑↑a / rationalZakGamma α q - ↑↑a / rationalZakGamma α q) = (0 : ℝ) := by ring
    have hhi : ((↑↑a + 1) / rationalZakGamma α q - ↑↑a / rationalZakGamma α q)
        = (rationalZakGamma α q)⁻¹ := by rw [← sub_div]; simp
    rwa [hlo, hhi] at this
  -- convert the fourier mode and reduce the integrand on the interval
  rw [fourierCoeffOn_eq_integral,
    show ((rationalZakGamma α q)⁻¹ - 0) = (rationalZakGamma α q)⁻¹ from sub_zero _]
  have hcongr : (∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹,
        (fourier (-k)) (↑ξ : AddCircle (rationalZakGamma α q)⁻¹) •
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ) r)
      = ∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹, (p : ℂ)⁻¹ *
          ∑ a : Fin p, H (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) := by
    have hslice_vol : ∀ᵐ ξ ∂(volume : Measure ℝ),
        ξ ∈ Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹ →
        ∀ a : Fin p,
          rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
            (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
          rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) :=
      (ae_restrict_iff' measurableSet_Ioc).mp hslice
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hslice_vol] with ξ hsliceξ hξ
    have hξmem : ξ ∈ Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹ := by
      rwa [Set.uIoc_of_le (le_of_lt (inv_pos.mpr hγ0))] at hξ
    have hzrect : ((s, ξ) : ℝ × ℝ) ∈ rationalPositiveFundamentalRect α p q := by
      rw [rationalPositiveFundamentalRect]; exact ⟨hs, hξmem⟩
    have hfourier : (fourier (-k)) (↑ξ : AddCircle (rationalZakGamma α q)⁻¹)
        = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (k : ℂ) * (rationalZakGamma α q : ℂ) * (ξ : ℂ)) := by
      rw [← zakPhase_eq_fourier_coe hγ0 (-k) ξ]; congr 1; push_cast; ring
    rw [hfourier, smul_eq_mul,
      gammaFiberField_mode_eq_sum hα hβ hpq_coprime hgap hαβ x hzrect r k
        (hsliceξ hξmem)]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hHdef]
    congr 2
    push_cast
    ring
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finset_sum (fun a _ => hHshift a),
    tiling_sum_integral hγ0 p H (fun m hm => hHint m hm), ← hηeq]
  simp only [hHdef]
  rw [baseFiber_mode_integral hα hβ hpq_coprime hgap hαβ x s r k hc, one_div, inv_inv]
  simp only [Complex.real_smul]
  push_cast
  rw [hγη]
  field_simp

/-- **The gamma fiber is an explicit γ-Zak transform (B4 value-match).** For a
compact-support representative `φ` of `x` (sample agreement `hsampleeq`), at a
base `s ∈ (0,η]` the abstract gamma fiber `X_{x,r}(s,·)` equals, a.e. on `(0,γ⁻¹]`,
the *explicit* γ-Zak `zakTransform γ φ (s+ηr)` — because both are `L²` with the same
window samples (fiberization coefficient = `x` sample =ᵐ `φ` sample =
`fourierCoeffOn(zakTransform)`).  This makes the quasi-periodicity `zakTransform_add_period`
applicable to the fiber, driving the `r→p−r` reindex. -/
lemma gammaFiberField_ae_eq_zakTransform {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : ℝ → ℂ) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q)) (r : Fin p)
    (hsampleeq : ∀ ℓ : ℤ, (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((r : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((r : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : Summable (fun k : ℤ => ‖φ ((s + rationalZakEta α p q * ((r : ℕ) : ℝ))
        - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (fun ξ => rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ) r)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)]
      (fun ξ => Zak.zakTransform (rationalZakGamma α q) φ
        (s + rationalZakEta α p q * ((r : ℕ) : ℝ)) ξ) := by
  have hγ0 : 0 < rationalZakGamma α q := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (p_pos_of_density hα hβ hgap hαβ).ne'
  have hηp : rationalZakEta α p q * (p : ℝ) = rationalZakGamma α q := by
    rw [rationalZakEta]; field_simp
  refine ae_eq_of_fourierCoeffOn_eq hγ0
    (gammaFiberField_component_memLp hα hβ hpq_coprime hgap hαβ x hs r hslice)
    (memLp_zakTransform hγ0 hφsum) (fun ℓ => ?_)
  rw [gammaFiberField_fourierCoeffOn hα hβ hpq_coprime hgap hαβ x hs r ℓ hc hslice,
    fourierCoeffOn_zakTransform_eq_sample hγ0 hφsum ℓ]
  have harg : s - rationalZakEta α p q * (((p : ℤ) * ℓ - (r : ℕ) : ℤ) : ℝ)
      = s + rationalZakEta α p q * ((r : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ) := by
    push_cast; rw [← hηp]; ring
  rw [harg]; exact hsampleeq ℓ

/-- **Matrix–fiber component as an explicit γ-Zak sum (B4 value-match).** Substituting
`gf =ᵐ zakTransform γ φ (s+ηs')` and the definition of the matrix entries, the
`t`-component of `M ·ᵥ gf` is a.e. the sum over the honest fiber index `s'` of
`conj(h1's γ-Zak at s+αt+γs'/p) · (φ's γ-Zak at s+ηs')`. -/
lemma matrixGammaFiber_ae_eq_zakSum {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : ℝ → ℂ) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q)) (t : Fin q)
    (hsampleeq : ∀ (s' : Fin p) (ℓ : ℤ), (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : ∀ s' : Fin p, Summable (fun k : ℤ =>
        ‖φ ((s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (fun ξ => (generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)]
      (fun ξ => ∑ s' : Fin p,
        (starRingEnd ℂ) (Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
            (s + α * ((t : ℕ) : ℝ) + rationalZakGamma α q * ((s' : ℕ) : ℝ) / (p : ℝ)) ξ)
          * Zak.zakTransform (rationalZakGamma α q) φ
            (s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) ξ) := by
  filter_upwards [ae_all_iff.mpr (fun s' : Fin p =>
    gammaFiberField_ae_eq_zakTransform hα hβ hpq_coprime hgap hαβ x φ hs s'
      (hsampleeq s') (hφsum s') hc hslice)] with ξ hξ
  rw [rationalZakMatrix_mulVec_apply]
  exact Finset.sum_congr rfl (fun s' _ => by rw [hξ s']; rfl)

/-- **Quasi-periodicity phase cancellation.** Shifting *both* γ-Zak factors of a
`conj · ` product by one period `γ` leaves the product unchanged: the two
`exp(±2πiγξ)` phases from `zakTransform_add_period` cancel.  This is what makes the
`s' → p−r` reindex phase-free on the wrapped (`+γ`) summands. -/
lemma zakTransform_conj_mul_add_period {γ : ℝ} (g f : ℝ → ℂ) (a b ξ : ℝ) :
    (starRingEnd ℂ) (Zak.zakTransform γ g (a + γ) ξ) * Zak.zakTransform γ f (b + γ) ξ
      = (starRingEnd ℂ) (Zak.zakTransform γ g a ξ) * Zak.zakTransform γ f b ξ := by
  have hphase : (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (ξ : ℂ)))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (ξ : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add,
      show (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (ξ : ℂ))
          + 2 * (Real.pi : ℂ) * Complex.I * (γ : ℂ) * (ξ : ℂ) = 0 from by
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring,
      Complex.exp_zero]
  rw [Zak.zakTransform_add_period, Zak.zakTransform_add_period, map_mul, mul_mul_mul_comm,
    hphase, one_mul]

/-- **The `s' → −r` reindex (B4 value-match).** The γ-Zak product sum over the
"upward" bases `A+s'η, B+s'η` (`s' ∈ Fin p`) equals the sum over the "downward"
bases `A−rη, B−rη` — the honest-fiber index set of the dense side.  Via the
`Fin p` negation bijection: for `s' = 0` the bases already match; for `s' ≠ 0` the
Fin-`p` wrap turns `A+s'η` into `(A−(p−s')η)+γ`, and the two `+γ` shifts cancel by
`zakTransform_conj_mul_add_period`. -/
lemma zakSum_reindex {γ : ℝ} {p : ℕ} (g f : ℝ → ℂ) (A B ξ : ℝ) :
    ∑ s' : Fin p, (starRingEnd ℂ)
          (Zak.zakTransform γ g (A + ((s' : ℕ) : ℝ) * (γ / p)) ξ)
        * Zak.zakTransform γ f (B + ((s' : ℕ) : ℝ) * (γ / p)) ξ
      = ∑ r : Fin p, (starRingEnd ℂ)
          (Zak.zakTransform γ g (A - ((r : ℕ) : ℝ) * (γ / p)) ξ)
        * Zak.zakTransform γ f (B - ((r : ℕ) : ℝ) * (γ / p)) ξ := by
  rw [← Equiv.sum_comp (Equiv.neg (Fin p)) (fun r : Fin p => (starRingEnd ℂ)
      (Zak.zakTransform γ g (A - ((r : ℕ) : ℝ) * (γ / p)) ξ)
    * Zak.zakTransform γ f (B - ((r : ℕ) : ℝ) * (γ / p)) ξ)]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  simp only [Equiv.neg_apply]
  have hwrap : (((-s' : Fin p) : ℕ) : ℝ)
      = (if (s' : ℕ) = 0 then 0 else (p : ℝ)) - ((s' : ℕ) : ℝ) := by
    rw [Fin.coe_neg]
    rcases eq_or_ne (s' : ℕ) 0 with h | h
    · rw [if_pos h, h]; simp
    · rw [if_neg h]; have hlt := s'.isLt; rw [Nat.mod_eq_of_lt (by omega), Nat.cast_sub hlt.le]
  rcases eq_or_ne (s' : ℕ) 0 with h | h
  · rw [hwrap, if_pos h]; congr 2 <;> ring
  · rw [hwrap, if_neg h]
    have hlt := s'.isLt
    have hpn : (p : ℝ) ≠ 0 := by
      have hp0 : 0 < p := by omega
      exact_mod_cast hp0.ne'
    have hA : A - ((p : ℝ) - ((s' : ℕ) : ℝ)) * (γ / p)
        = (A + ((s' : ℕ) : ℝ) * (γ / p)) - γ := by field_simp; ring
    have hB : B - ((p : ℝ) - ((s' : ℕ) : ℝ)) * (γ / p)
        = (B + ((s' : ℕ) : ℝ) * (γ / p)) - γ := by field_simp; ring
    rw [hA, hB, ← zakTransform_conj_mul_add_period g f
      ((A + ((s' : ℕ) : ℝ) * (γ / p)) - γ) ((B + ((s' : ℕ) : ℝ) * (γ / p)) - γ) ξ]
    congr 2 <;> ring

/-- **The reindexed matrix–fiber product (B4).** Combining `matrixGammaFiber_ae_eq_zakSum`
with the `s' → −r` reindex `zakSum_reindex`: the `t`-component is a.e. the "downward"
γ-Zak product sum over bases `s − rβ⁻¹` (`= s − rη`), exactly the honest-fiber index
set of the dense Zibulski–Zeevi side. -/
lemma matrixGammaFiber_ae_eq_zakSum_down {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : ℝ → ℂ) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q)) (t : Fin q)
    (hsampleeq : ∀ (s' : Fin p) (ℓ : ℤ), (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : ∀ s' : Fin p, Summable (fun k : ℤ =>
        ‖φ ((s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (fun ξ => (generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)]
      (fun ξ => ∑ r : Fin p,
        (starRingEnd ℂ) (Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
            ((s + α * ((t : ℕ) : ℝ)) - ((r : ℕ) : ℝ) * β⁻¹) ξ)
          * Zak.zakTransform (rationalZakGamma α q) φ (s - ((r : ℕ) : ℝ) * β⁻¹) ξ) := by
  refine (matrixGammaFiber_ae_eq_zakSum hα hβ hpq_coprime hgap hαβ x φ hs t
    hsampleeq hφsum hc hslice).trans (Filter.Eventually.of_forall (fun ξ => ?_))
  dsimp only
  have hηp : rationalZakEta α p q * (p : ℝ) = rationalZakGamma α q :=
    rationalZakEta_mul_p_eq_gamma hα hβ hgap hαβ
  have hηβ : rationalZakEta α p q = β⁻¹ := rationalZakEta_eq_inv_beta hα hβ hgap hαβ
  have hp : (p : ℝ) ≠ 0 := by
    have := p_pos_of_density hα hβ hgap hαβ; exact_mod_cast this.ne'
  have hγη : rationalZakGamma α q / (p : ℝ) = rationalZakEta α p q := by
    rw [← hηp]; field_simp
  rw [Finset.sum_congr rfl (fun (s' : Fin p) _ => show
      (starRingEnd ℂ) (Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
          (s + α * ((t : ℕ) : ℝ) + rationalZakGamma α q * ((s' : ℕ) : ℝ) / (p : ℝ)) ξ)
        * Zak.zakTransform (rationalZakGamma α q) φ
            (s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) ξ
      = (starRingEnd ℂ) (Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
          ((s + α * ((t : ℕ) : ℝ)) + ((s' : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ))) ξ)
        * Zak.zakTransform (rationalZakGamma α q) φ
            (s + ((s' : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ))) ξ from by
      have e1 : s + α * ((t : ℕ) : ℝ) + rationalZakGamma α q * ((s' : ℕ) : ℝ) / (p : ℝ)
          = (s + α * ((t : ℕ) : ℝ)) + ((s' : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ)) := by
        ring
      have e2 : s + rationalZakEta α p q * ((s' : ℕ) : ℝ)
          = s + ((s' : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ)) := by rw [hγη]; ring
      rw [e1, e2])]
  rw [zakSum_reindex (generalizedH1 τ) φ (s + α * ((t : ℕ) : ℝ)) s ξ]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e3 : (s + α * ((t : ℕ) : ℝ)) - ((r : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ))
      = (s + α * ((t : ℕ) : ℝ)) - ((r : ℕ) : ℝ) * β⁻¹ := by rw [hγη, hηβ]
  have e4 : s - ((r : ℕ) : ℝ) * (rationalZakGamma α q / (p : ℝ))
      = s - ((r : ℕ) : ℝ) * β⁻¹ := by rw [hγη, hηβ]
  rw [e3, e4]

/-- **Per-`(t,s)` value-match (B4 capstone).** For `s` in the base strip and a
compact-support window `φ` sampling `x`, the spatial ℓ²-energy of the regrouped LHS
integrand `A_{ℓ,t}(s)` equals `γ` times the ξ-integral of `‖(M·gf)_t‖²` — the
inner-product (Euclidean) matrix-energy density.  This fuses the dense Zibulski–Zeevi
ξ-identity (`dense_strip_energy_eq_xi_integral`) with the fiberization value-match:
the dense ξ-integrand `∑_r X_r·conj(P_r)` is a.e. the conjugate of `(M·gf)_t`
(`X_r = conj(φ γ-Zak)` by `conj_zakTransform_compactSample`, `conj(P_r) = h₁ γ-Zak`
by `window_conj_ae_eq_zakTransform_h1`, and the reindexed `(M·gf)_t` by
`matrixGammaFiber_ae_eq_zakSum_down`), so the two have equal norm. -/
lemma dense_energy_eq_matrix_energy {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {φ : ℝ → ℂ} (hφ : HasCompactSupport φ)
    (t : Fin q) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q))
    (hsampleeq : ∀ (s' : Fin p) (ℓ : ℤ), (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : ∀ s' : Fin p, Summable (fun k : ℤ =>
        ‖φ ((s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (∑' ℓ : ℤ, ‖∑ r : Fin p, ∑' j : ℤ,
        (starRingEnd ℂ) (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (j : ℝ) * rationalZakGamma α q)) *
          generalizedH1 τ ((s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ))
            + ((j - ℓ : ℤ) : ℝ) * rationalZakGamma α q)‖ ^ 2)
      = rationalZakGamma α q * ∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2 := by
  have hq : 0 < q := q_pos_of_gap hgap
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  obtain ⟨Pr, u, hPrmem, hPrcoeff, husupp, _hℓsummable, hspatial⟩ :=
    dense_strip_energy_eq_xi_integral (p := p) (β := β) hτ hα hq hφ t s
  rw [hspatial]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le (le_of_lt (inv_pos.mpr hγ))]
  have hM := matrixGammaFiber_ae_eq_zakSum_down (τ := τ)
    hα hβ hpq_coprime hgap hαβ x φ hs t
    hsampleeq hφsum hc hslice
  have hPr_r : ∀ r : Fin p,
      (fun ξ => (starRingEnd ℂ) (Pr r ξ))
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)]
        (fun ξ => Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
          (s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ)) ξ) :=
    fun r => window_conj_ae_eq_zakTransform_h1 hτ hγ
      (s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ)) (Pr r) (hPrmem r) (hPrcoeff r)
  refine (ae_restrict_iff' measurableSet_Ioc).mp ?_
  filter_upwards [hM, ae_all_iff.mpr hPr_r] with ξ hMξ hPrξ
  rw [hMξ]
  have hsum : (∑ r : Fin p,
      (∑ b ∈ u r, (starRingEnd ℂ)
          (φ ((s - ((r : ℕ) : ℝ) * β⁻¹) + (b : ℝ) * rationalZakGamma α q)) *
          Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I *
            ((rationalZakGamma α q : ℂ) * (b : ℂ) * (ξ : ℂ)))) *
        (starRingEnd ℂ) (Pr r ξ))
      = (starRingEnd ℂ) (∑ r : Fin p,
          (starRingEnd ℂ) (Zak.zakTransform (rationalZakGamma α q) (generalizedH1 τ)
              ((s + α * ((t : ℕ) : ℝ)) - ((r : ℕ) : ℝ) * β⁻¹) ξ)
            * Zak.zakTransform (rationalZakGamma α q) φ (s - ((r : ℕ) : ℝ) * β⁻¹) ξ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← conj_zakTransform_compactSample (s - ((r : ℕ) : ℝ) * β⁻¹) ξ (u r) (husupp r),
      hPrξ r, map_mul, Complex.conj_conj,
      show s - ((r : ℕ) : ℝ) * β⁻¹ + α * ((t : ℕ) : ℝ)
        = s + α * ((t : ℕ) : ℝ) - ((r : ℕ) : ℝ) * β⁻¹ from by ring]
    ring
  rw [hsum, Complex.norm_conj]

/-- **Per-`s` regrouped-strip energy = matrix ξ-energy.** The exact `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ)`
strip integrand (the `ℓ`-energy of `∑'_k conj φ · h₁_element(qℓ−t)`) equals `γ ∫_ξ
‖(M·gf)_t‖²`.  Just `inner_periodization_p_strip_h1` (rewrite the `k`-periodization into
the `p`-strip `∑_r ∑'_j` form) followed by `dense_energy_eq_matrix_energy`. -/
lemma regrouped_strip_energy_eq_matrix {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {φ : ℝ → ℂ} (hφ : HasCompactSupport φ)
    (t : Fin q) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q))
    (hsampleeq : ∀ (s' : Fin p) (ℓ : ℤ), (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : ∀ s' : Fin p, Summable (fun k : ℤ =>
        ‖φ ((s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (∑' ℓ : ℤ, ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0
          (s + (k : ℝ) * β⁻¹)‖ ^ 2)
      = rationalZakGamma α q * ∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2 := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq : 0 < q := q_pos_of_gap hgap
  rw [tsum_congr (fun ℓ : ℤ => congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (inner_periodization_p_strip_h1 hp hq hβ hαβ hφ t ℓ s))]
  exact dense_energy_eq_matrix_energy hτ hα hβ hpq_coprime hgap hαβ x hφ t hs
    hsampleeq hφsum hc hslice

/-- **Per-`s` `ℓ`-summability of the regrouped strip energy.** The `ℓ`-series
`‖A_{ℓ,t}(s)‖²` (the `h₁_element` form) is summable — via `inner_periodization_p_strip_h1`
it is the `∑_r ∑'_j` form whose summability `dense_strip_energy_eq_xi_integral` now
exposes (Fourier `ℓ²`, `summable_gamma_step34_vector`).  This is the per-`s` summability
the ENNReal `ofReal`/`tsum` interchange consumes. -/
lemma summable_regrouped_strip_ell {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) (t : Fin q) (s : ℝ) :
    Summable (fun ℓ : ℤ => ‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β ((q : ℤ) * ℓ - (((t : Fin q) : ℕ) : ℤ)) 0
          (s + (k : ℝ) * β⁻¹)‖ ^ 2) := by
  have hp : 0 < p := p_pos_of_density hα hβ hgap hαβ
  have hq : 0 < q := q_pos_of_gap hgap
  obtain ⟨Pr, u, _, _, _, hℓsummable, _⟩ :=
    dense_strip_energy_eq_xi_integral (p := p) (β := β) hτ hα hq hφ t s
  exact hℓsummable.congr (fun ℓ => congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (inner_periodization_p_strip_h1 hp hq hβ hαβ hφ t ℓ s).symm)

/-- **Per-`s` ENNReal `m`-sum identity.** With the compact-support sample hypotheses at
`s`, the ENNReal `m`-sum of `ofReal ‖A_m(s)‖²` regroups (via `m = qℓ − t`, unconditional
in ENNReal) into `∑_t ofReal (γ ∫_ξ ‖(M·gf)_t‖²)` — the per-`s` value-match, lifted to
ENNReal so no Bessel summability is needed. -/
lemma ennreal_msum_sq_eq_matrix_of_hyps {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {φ : ℝ → ℂ} (hφ : HasCompactSupport φ)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q))
    (hsampleeq : ∀ (s' : Fin p) (ℓ : ℤ), (⇑x : ℝ → ℂ)
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ))
      = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)))
    (hφsum : ∀ s' : Fin p, Summable (fun k : ℤ =>
        ‖φ ((s + rationalZakEta α p q * ((s' : ℕ) : ℝ)) - rationalZakGamma α q * (k : ℝ))‖))
    (hc : Summable (fun m : ℤ =>
        ‖(⇑x : ℝ → ℂ) (s - rationalZakEta α p q * (m : ℝ))‖ ^ 2))
    (hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
      ∀ a : Fin p,
        rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
          (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
        rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
          (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q)) :
    (∑' m : ℤ, ENNReal.ofReal (‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2))
      = ∑ t : Fin q, ENNReal.ofReal (rationalZakGamma α q *
          ∫ ξ in (0 : ℝ)..(rationalZakGamma α q)⁻¹,
            ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
              rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2) := by
  have hq : 0 < q := q_pos_of_gap hgap
  rw [tsum_int_qMulSubFinEquiv hq, ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  dsimp only
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => sq_nonneg _)
      (summable_regrouped_strip_ell hτ hα hβ hpq_coprime hgap hαβ hφ t s),
    regrouped_strip_energy_eq_matrix hτ hα hβ hpq_coprime hgap hαβ x hφ t hs
      hsampleeq hφsum hc hslice]

/-- **CLM `MemLp` foundation.** The matrix–fiber product
`z ↦ generalizedRationalZakMatrix τ z *ᵥ gammaFiberField x z` is an `L²(ℝ²; ℂ^q)` element. -/
lemma matrixGammaFiber_memLp {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun z => generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) 2
      (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨B, hB0, hB⟩ :=
    rationalZakMatrix_uniform_bound_gaussian hτ
      (rationalZakGamma_pos hα (q_pos_of_gap hgap))
  have hMcont : Continuous (generalizedRationalZakMatrix τ α p q) :=
    continuous_conjTranspose_matrix_field
      (continuous_rationalZakPMatrixH1_gaussian hτ
        (rationalZakGamma_pos hα (q_pos_of_gap hgap)))
  have hMaesm : ∀ i j, AEStronglyMeasurable
      (fun z : ℝ × ℝ => generalizedRationalZakMatrix τ α p q z i j) (volume : Measure (ℝ × ℝ)) :=
    fun i j => ((continuous_apply j).comp ((continuous_apply i).comp hMcont)).aestronglyMeasurable
  have hvaesm : ∀ r, AEStronglyMeasurable
      (fun z : ℝ × ℝ => rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z r)
      (volume : Measure (ℝ × ℝ)) :=
    Zak.vector_components_aestronglyMeasurable _
      (rationalPositiveGammaFiberField_aestronglyMeasurable hα hβ hpq_coprime hgap hαβ x)
  have haesm : AEStronglyMeasurable (fun z => generalizedRationalZakMatrix τ α p q z *ᵥ
      rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) (volume : Measure (ℝ × ℝ)) :=
    Zak.matrix_mulVec_aestronglyMeasurable_of_components _ _ hMaesm hvaesm
  rw [memLp_two_iff_integrable_sq_norm haesm]
  have hηγ : 0 < rationalZakEta α p q * rationalZakGamma α q :=
    mul_pos (rationalZakEta_pos hα hβ hgap hαβ) (rationalZakGamma_pos hα (q_pos_of_gap hgap))
  refine Integrable.mono'
    ((rationalPositiveFiberField_component_energy_integrable hα hβ hpq_coprime hgap hαβ x).const_mul B)
    (haesm.norm.pow 2) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgen := gammaMatrixEnergy_le_of_matrix_bound hα hβ hpq_coprime hgap hαβ hB0 hB x z
  have hgen' : rationalZakEta α p q * rationalZakGamma α q *
        ‖generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
      ≤ rationalZakEta α p q * rationalZakGamma α q *
        (B * ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by
    calc rationalZakEta α p q * rationalZakGamma α q *
          ‖generalizedRationalZakMatrix τ α p q z *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
        = generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z := rfl
      _ ≤ rationalZakEta α p q * rationalZakGamma α q * B *
            ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := hgen
      _ = rationalZakEta α p q * rationalZakGamma α q *
            (B * ∑ r : Fin p, ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by
            ring
  exact le_of_mul_le_mul_left hgen' hηγ

/-- A.e. additivity of the matrix–fiber product (obligation-2 `map_add` input). -/
lemma matrixGammaFiber_add_ae {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x y : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun z => generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ (x + y) z)
      =ᵐ[(volume : Measure (ℝ × ℝ))]
      fun z => generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z
        + generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ y z := by
  filter_upwards [rationalPositiveGammaFiberField_add_ae hα hβ hpq_coprime hgap hαβ x y] with z hz
  rw [hz, Matrix.mulVec_add]

/-- A.e. homogeneity of the matrix–fiber product (obligation-2 `map_smul` input). -/
lemma matrixGammaFiber_smul_ae {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (c : ℂ) (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun z => generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ (c • x) z)
      =ᵐ[(volume : Measure (ℝ × ℝ))]
      fun z => c • (generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) := by
  filter_upwards [rationalPositiveGammaFiberField_smul_ae hα hβ hpq_coprime hgap hαβ c x] with z hz
  rw [hz, Matrix.mulVec_smul]

/-! ## Residual obligations (ALL DISCHARGED)

The corrected (Euclidean) coefficient identity is reduced to the three obligations
below — `productCoeffEnergy_continuous`, `gammaMatrixEuclideanEnergyIntegral_continuous`,
and `exists_dense_eqOn` — and **all three are now proved** (no `sorry`).  They assemble
into `rationalPositiveGammaMatrix_coeff_identity` at the end of this file, which replaces
the former (false) sup-norm axiom of the same name.  Nothing depends on `sorryAx`. -/

-- `productCoeffEnergy_continuous` (obligation 1, LHS continuity) is proved below,
-- after the dense identity machinery it depends on (the Gabor analysis operator is
-- bounded, via the Fatou/lsc argument from the corrected RHS bound).

/-- The reinterpretation CLM sending the sup-normed `Fin q → ℂ` to the
inner-product `EuclideanSpace ℂ (Fin q)` (same underlying vector). -/
noncomputable def toEuclidCLM (q : ℕ) :
    (Fin q → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  (WithLp.linearEquiv 2 ℂ (Fin q → ℂ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma norm_toEuclidCLM_sq (q : ℕ) (v : Fin q → ℂ) :
    ‖toEuclidCLM q v‖ ^ 2 = ∑ t : Fin q, ‖v t‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rfl

/-- **The corrected (Euclidean) Zibulski–Zeevi matrix-energy integral.** Uses the
inner-product component sum `∑_t |(M·gf)_t|²` rather than the sup norm of
`generalizedRationalPositiveGammaMatrixEnergy (τ := τ)`. This is the mathematically correct RHS of the
coefficient identity (see the sup-vs-Euclidean note; the sup version is strictly
smaller for `q ≥ 2`). -/
noncomputable def gammaMatrixEuclideanEnergyIntegral
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  ∫ z, rationalZakEta α p q * rationalZakGamma α q *
      ∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2
    ∂(volume : Measure (ℝ × ℝ))

/-- **Corrected RHS continuity.** The Euclidean matrix-energy integral is a
continuous quadratic form, via the `L²(ℝ²; EuclideanSpace ℂ (Fin q))` CLM
`x ↦ toEuclidCLM (generalizedRationalZakMatrix τ ·ᵥ gammaFiberField x)`. -/
lemma gammaMatrixEuclideanEnergyIntegral_continuous
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    Continuous (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ) := by
  have hη : 0 < rationalZakEta α p q := rationalZakEta_pos hα hβ hgap hαβ
  have hγ : 0 < rationalZakGamma α q := rationalZakGamma_pos hα (q_pos_of_gap hgap)
  obtain ⟨B, hB0, hB⟩ := rationalZakMatrix_uniform_bound_gaussian hτ hγ
  have hmemV := fun x => (matrixGammaFiber_memLp hτ hα hβ hpq_coprime hgap hαβ x).continuousLinearMap_comp
    (toEuclidCLM q)
  have hVnorm : ∀ x, ‖(hmemV x).toLp‖ ^ 2
      = ∫ z, ∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2
        ∂(volume : Measure (ℝ × ℝ)) := by
    intro x
    rw [Lp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [(hmemV x).coeFn_toLp] with z hz
    rw [hz, norm_toEuclidCLM_sq]
  have henergy : ∀ x, gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x
      = (rationalZakEta α p q * rationalZakGamma α q) * ‖(hmemV x).toLp‖ ^ 2 := by
    intro x
    rw [gammaMatrixEuclideanEnergyIntegral, hVnorm x, ← integral_const_mul]
  -- pointwise bound  ∑_t |(M gf)_t|² ≤ q·B·∑_r |v_r|²
  have hptwise : ∀ x z, (∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      ≤ (q : ℝ) * B * ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := by
    intro x z
    calc (∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
              rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
        ≤ (q : ℝ) * ‖generalizedRationalZakMatrix τ α p q z *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2 := by
          simpa using finiteVector_sum_norm_sq_le_card_mul_norm_sq
            (generalizedRationalZakMatrix τ α p q z *ᵥ
              rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z)
      _ ≤ (q : ℝ) * (B * ∑ r : Fin p,
            ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ (q : ℝ))
          have hen := gammaMatrixEnergy_le_of_matrix_bound hα hβ hpq_coprime hgap hαβ hB0 hB x z
          have hle : rationalZakEta α p q * rationalZakGamma α q *
                ‖generalizedRationalZakMatrix τ α p q z *ᵥ
                  rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
              ≤ rationalZakEta α p q * rationalZakGamma α q *
                (B * ∑ r : Fin p,
                  ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by
            calc rationalZakEta α p q * rationalZakGamma α q *
                  ‖generalizedRationalZakMatrix τ α p q z *ᵥ
                    rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2
                = generalizedRationalPositiveGammaMatrixEnergy (τ := τ) hα hβ hpq_coprime hgap hαβ x z := rfl
              _ ≤ rationalZakEta α p q * rationalZakGamma α q * B *
                    ∑ r : Fin p,
                      ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := hen
              _ = rationalZakEta α p q * rationalZakGamma α q *
                    (B * ∑ r : Fin p,
                      ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2) := by ring
          exact le_of_mul_le_mul_left hle (mul_pos hη hγ)
      _ = (q : ℝ) * B * ∑ r : Fin p,
            ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2 := by ring
  -- linear map V into EuclideanSpace-valued L²
  let V : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure (ℝ × ℝ)) :=
    { toFun := fun x => (hmemV x).toLp
      map_add' := fun x y => by
        rw [← MemLp.toLp_add (hmemV x) (hmemV y)]
        refine MemLp.toLp_congr (hmemV (x + y)) _ ?_
        filter_upwards [matrixGammaFiber_add_ae hα hβ hpq_coprime hgap hαβ x y] with z hz
        simp only [Pi.add_apply]
        rw [hz, map_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul c (hmemV x)]
        refine MemLp.toLp_congr (hmemV (c • x)) _ ?_
        filter_upwards [matrixGammaFiber_smul_ae hα hβ hpq_coprime hgap hαβ c x] with z hz
        simp only [Pi.smul_apply]
        rw [hz, map_smul] }
  -- boundedness
  have hVbound : ∀ x, ‖V x‖ ≤ Real.sqrt ((q : ℝ) * B / rationalZakEta α p q) * ‖x‖ := by
    intro x
    have hintL : Integrable (fun z => ∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
        (volume : Measure (ℝ × ℝ)) := by
      have := (hmemV x).integrable_norm_pow (p := 2) (by norm_num)
      refine this.congr ?_
      filter_upwards with z using norm_toEuclidCLM_sq q _
    have hintR : Integrable (fun z => (q : ℝ) * B * ∑ r : Fin p,
          ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2)
        (volume : Measure (ℝ × ℝ)) :=
      (rationalPositiveFiberField_component_energy_integrable hα hβ hpq_coprime hgap hαβ x).const_mul _
    have hsq : ‖(hmemV x).toLp‖ ^ 2
        ≤ (Real.sqrt ((q : ℝ) * B / rationalZakEta α p q) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hVnorm x]
      calc ∫ z, ∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
                rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2
              ∂(volume : Measure (ℝ × ℝ))
          ≤ ∫ z, (q : ℝ) * B * ∑ r : Fin p,
                ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2
              ∂(volume : Measure (ℝ × ℝ)) := integral_mono hintL hintR (fun z => hptwise x z)
        _ = (q : ℝ) * B * ∫ z, ∑ r : Fin p,
                ‖rationalPositiveFiberField hα hβ hpq_coprime hgap hαβ x z r‖ ^ 2
              ∂(volume : Measure (ℝ × ℝ)) := by rw [integral_const_mul]
        _ = (q : ℝ) * B / rationalZakEta α p q * ‖x‖ ^ 2 := by
            rw [rationalPositiveFiberField_component_energy_identity_scaled]
            field_simp
    calc ‖V x‖ = Real.sqrt (‖(hmemV x).toLp‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt ((q : ℝ) * B / rationalZakEta α p q) * ‖x‖) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((q : ℝ) * B / rationalZakEta α p q) * ‖x‖ := Real.sqrt_sq (by positivity)
  have hcont : Continuous (fun x => (hmemV x).toLp) :=
    (V.mkContinuous (Real.sqrt ((q : ℝ) * B / rationalZakEta α p q)) hVbound).continuous
  have hc : Continuous fun x =>
      (rationalZakEta α p q * rationalZakGamma α q) * ‖(hmemV x).toLp‖ ^ 2 :=
    (hcont.norm.pow 2).const_mul _
  exact hc.congr (fun x => (henergy x).symm)

/-- **Euclidean Bessel bound.** `gammaMatrixEuclideanEnergyIntegral x ≤ qγB‖x‖²` for a
fixed `B` (all `x`).  From the sup-norm bound `gammaMatrixEnergyIntegral_le` and the
finite comparison `∑_t ‖v_t‖² ≤ q ‖v‖²_sup`.  Feeds the Fatou step for obligation 1. -/
lemma gammaMatrixEuclideanEnergyIntegral_le {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := gammaMatrixEnergyIntegral_le hτ hα hβ hpq_coprime hgap hαβ
  have hηγ : 0 ≤ rationalZakEta α p q * rationalZakGamma α q :=
    mul_nonneg (rationalZakEta_pos hα hβ hgap hαβ).le
      (rationalZakGamma_pos hα (q_pos_of_gap hgap)).le
  refine ⟨(q : ℝ) * (rationalZakGamma α q * B), mul_nonneg (Nat.cast_nonneg q)
    (mul_nonneg (rationalZakGamma_pos hα (q_pos_of_gap hgap)).le hB0), fun x => ?_⟩
  have hmem := matrixGammaFiber_memLp hτ hα hβ hpq_coprime hgap hαβ x
  have hmemE := hmem.continuousLinearMap_comp (toEuclidCLM q)
  have hle : gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x
      ≤ (q : ℝ) * gammaMatrixEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x := by
    rw [gammaMatrixEuclideanEnergyIntegral, gammaMatrixEnergyIntegral, ← integral_const_mul]
    refine integral_mono ((Integrable.const_mul
        ((hmemE.integrable_norm_pow (p := 2) (by norm_num)).congr
          (Filter.Eventually.of_forall (fun z => norm_toEuclidCLM_sq q _))) _))
      ((Integrable.const_mul ((hmem.integrable_norm_pow (p := 2) (by norm_num)).const_mul _) _))
      (fun z => ?_)
    unfold generalizedRationalPositiveGammaMatrixEnergy
    rw [show (q : ℝ) *
        (rationalZakEta α p q * rationalZakGamma α q *
          ‖generalizedRationalZakMatrix τ α p q z *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2)
      = rationalZakEta α p q * rationalZakGamma α q * ((q : ℝ) *
          ‖generalizedRationalZakMatrix τ α p q z *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z‖ ^ 2) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ hηγ
    have := finiteVector_sum_norm_sq_le_card_mul_norm_sq
      (generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z)
    simpa using this
  calc gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x
      ≤ (q : ℝ) * gammaMatrixEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x := hle
    _ ≤ (q : ℝ) * (rationalZakGamma α q * B * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hB x) (by positivity)
    _ = (q : ℝ) * (rationalZakGamma α q * B) * ‖x‖ ^ 2 := by ring

/-- The Euclidean matrix-energy integrand `∑_t ‖(M·gf)_t‖²` vanishes off the
fundamental rectangle (the fiber field, hence the whole matrix product, is `0`). -/
lemma euclideanEnergyIntegrand_eq_zero_of_not_mem
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) {z : ℝ × ℝ}
    (hz : z ∉ rationalPositiveFundamentalRect α p q) :
    ∑ t : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2 = 0 := by
  unfold rationalPositiveGammaFiberField
  rw [rationalPositiveFiberField_eq_zero_of_not_mem hα hβ hpq_coprime hgap hαβ x hz]
  simp [Matrix.mulVec_zero]

/-- **Euclidean matrix-energy as an iterated integral over the rectangle.**  The
full-plane integral collapses to the fundamental rectangle (integrand `0` outside),
then Fubini (`setIntegral_prod`) splits it into the `s`-then-`ξ` iterated integral and
the finite `t`-sum comes out. This is the exact shape the LHS Zibulski–Zeevi assembly
produces (`ηγ ∑_t ∫_s ∫_ξ ‖(M·gf)_t‖²`). -/
lemma gammaMatrixEuclideanEnergyIntegral_eq_iterated
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x
      = rationalZakEta α p q * rationalZakGamma α q *
        ∑ t : Fin q, ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
          ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
            ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
              rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2 := by
  have hmem := matrixGammaFiber_memLp hτ hα hβ hpq_coprime hgap hαβ x
  have hmemE := hmem.continuousLinearMap_comp (toEuclidCLM q)
  -- each component's ‖·‖² is integrable (dominated by the Euclidean sum, which is integrable)
  have hGint : Integrable (fun z => ∑ t : Fin q,
      ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    refine (hmemE.integrable_norm_pow (p := 2) (by norm_num)).congr ?_
    filter_upwards with z using (norm_toEuclidCLM_sq q _)
  have hFmeas : ∀ t : Fin q, AEStronglyMeasurable
      (fun z => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := fun t =>
    (((continuous_apply t).comp_aestronglyMeasurable hmem.1).norm.pow 2)
  have hFint : ∀ t : Fin q, Integrable
      (fun z => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    intro t
    refine hGint.mono' (hFmeas t) (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum
      (f := fun t' : Fin q => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t'‖ ^ 2)
      (fun t' _ => sq_nonneg _) (Finset.mem_univ t)
  rw [gammaMatrixEuclideanEnergyIntegral, integral_const_mul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
      euclideanEnergyIntegrand_eq_zero_of_not_mem hα hβ hpq_coprime hgap hαβ x hz)]
  congr 1
  rw [MeasureTheory.integral_finset_sum _ (fun t _ => (hFint t).integrableOn)]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [rationalPositiveFundamentalRect,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume
      from Measure.volume_eq_prod ℝ ℝ]
  exact setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact (hFint t).integrableOn)

/-- **Matrix-energy strip marginal is integrable.** The `s`-marginal
`s ↦ ∫_ξ ‖(M·gf(s,ξ))_t‖²` over the fiber `(0,γ⁻¹]` is integrable on the base strip
`(0,η]` — Fubini (`Integrable.integral_prod_left`) applied to the component `L²`
integrand.  Consumed by the ENNReal outer wrapper's per-`t` `ofReal ∫` conversion. -/
lemma matrixComponent_marginal_integrableOn {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (t : Fin q) :
    IntegrableOn (fun s => ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
        ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
          rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2)
      (Set.Ioc (0 : ℝ) (rationalZakEta α p q)) volume := by
  have hmem := matrixGammaFiber_memLp hτ hα hβ hpq_coprime hgap hαβ x
  have hFint : Integrable (fun z => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
      rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    have hmemE := hmem.continuousLinearMap_comp (toEuclidCLM q)
    have hGint : Integrable (fun z => ∑ t' : Fin q, ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t'‖ ^ 2)
        (volume : Measure (ℝ × ℝ)) :=
      (hmemE.integrable_norm_pow (p := 2) (by norm_num)).congr
        (Filter.Eventually.of_forall (fun z => norm_toEuclidCLM_sq q _))
    refine hGint.mono' (((continuous_apply t).comp_aestronglyMeasurable hmem.1).norm.pow 2)
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum
      (f := fun t' : Fin q => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
        rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t'‖ ^ 2)
      (fun t' _ => sq_nonneg _) (Finset.mem_univ t)
  have hprod : (volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q) ×ˢ Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)
      = (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
          (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hint2 : Integrable (fun z => ‖(generalizedRationalZakMatrix τ α p q z *ᵥ
      rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x z) t‖ ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (rationalZakEta α p q))).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹))) := by
    rw [← hprod]; exact hFint.integrableOn
  exact hint2.integral_prod_left

/-- **ℝ-level final combine.** The iterated integral produced by the ENNReal LHS
assembly (`β⁻¹ ∫_s γ ∫_ξ ‖(M·gf)_t‖²`, summed over `t`) is exactly
`gammaMatrixEuclideanEnergyIntegral` — via `eq_iterated`, pulling the `γ` constant out
of `∫_s` and `β⁻¹ = η`. -/
lemma iterated_eq_euclidean {α β : ℝ} {p q : ℕ} [NeZero q]
    (hτ : 0 < τ.im) (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑ t : Fin q, β⁻¹ * ∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q),
        rationalZakGamma α q * ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2)
      = gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x := by
  rw [gammaMatrixEuclideanEnergyIntegral_eq_iterated hτ hα hβ hpq_coprime hgap hαβ x,
    rationalZakEta_eq_inv_beta hα hβ hgap hαβ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [integral_const_mul]
  ring

/-- **The ENNReal coefficient identity (compact-support class).** For `x` with a
continuous compact-support representative `φ`, the ENNReal coefficient energy
`∑'_{mn} ofReal ‖⟨x,g_{mn}⟩‖²` equals `ofReal(gammaMatrixEuclideanEnergyIntegral x)`.
Because ENNReal `tsum`/Tonelli are unconditional, **no Gabor Bessel bound is needed** —
this is the whole point of the ENNReal route. Assembled from: B1 per-`m` Parseval
(`gabor_nsum_eq_spatial`), the per-`s` value-match (`ennreal_msum_sq_eq_matrix_of_hyps`),
and the iterated-integral collapse (`iterated_eq_euclidean`). -/
lemma productCoeffEnergy_ennreal_eq_euclidean {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : C(ℝ, ℂ)) (hφ_cs : HasCompactSupport ⇑φ)
    (hxφ : (x : ℝ → ℂ) =ᵐ[volume] ⇑φ) :
    (∑' mn : ℤ × ℤ, ENNReal.ofReal
        (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2))
      = ENNReal.ofReal (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x) := by
  have hq : 0 < q := q_pos_of_gap hgap
  have hη : rationalZakEta α p q = β⁻¹ := rationalZakEta_eq_inv_beta hα hβ hgap hαβ
  have hγpos : 0 < rationalZakGamma α q := rationalZakGamma_pos hα hq
  have hβ0 : (0 : ℝ) ≤ β⁻¹ := (inv_pos.mpr hβ).le
  -- measurability of `ofReal ‖A_m ·‖²` on the strip
  have hAmeas : ∀ m : ℤ, AEMeasurable (fun s => ENNReal.ofReal
      (‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
        generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2))
      (volume.restrict (Set.Ioc (0 : ℝ) β⁻¹)) := fun m =>
    ((strip_amplitude_sq_integrableOn α β hβ m φ.continuous
      hφ_cs).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  rw [ENNReal.tsum_prod']
  have hstep2 : ∀ m : ℤ, (∑' n : ℤ, ENNReal.ofReal
      (‖inner ℂ x (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2))
      = ENNReal.ofReal β⁻¹ * ∫⁻ s in Set.Ioc (0 : ℝ) β⁻¹, ENNReal.ofReal
        (‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
          generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2) := by
    intro m
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _)
        (summable_gabor_nsum α β hβ m x φ hφ_cs hxφ),
      gabor_nsum_eq_spatial α β hβ m x φ hφ_cs hxφ,
      ENNReal.ofReal_mul hβ0, ofReal_integral_eq_lintegral_ofReal
        (strip_amplitude_sq_integrableOn α β hβ m φ.continuous hφ_cs)
        (Filter.Eventually.of_forall (fun s => sq_nonneg _))]
  simp_rw [hstep2]
  rw [ENNReal.tsum_mul_left, ← lintegral_tsum hAmeas,
    show Set.Ioc (0 : ℝ) β⁻¹ = Set.Ioc (0 : ℝ) (rationalZakEta α p q) from by rw [hη]]
  have hae : (fun s => ∑' m : ℤ, ENNReal.ofReal
        (‖∑' k : ℤ, (starRingEnd ℂ) (φ (s + (k : ℝ) * β⁻¹)) *
          generalizedH1Element τ α β m 0 (s + (k : ℝ) * β⁻¹)‖ ^ 2))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (rationalZakEta α p q))]
      (fun s => ∑ t : Fin q, ENNReal.ofReal (rationalZakGamma α q *
        ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2)) := by
    have hsampleae : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakEta α p q))),
        ∀ (s' : Fin p) (ℓ : ℤ),
        (⇑x : ℝ → ℂ) (s + rationalZakEta α p q * ((s' : ℕ) : ℝ)
            - rationalZakGamma α q * (ℓ : ℝ))
        = φ (s + rationalZakEta α p q * ((s' : ℕ) : ℝ) - rationalZakGamma α q * (ℓ : ℝ)) :=
      ae_restrict_of_ae (ae_all_iff.mpr (fun s' => ae_forall_sample_eq (rationalZakGamma α q)
        (rationalZakEta α p q * ((s' : ℕ) : ℝ)) x φ hxφ))
    filter_upwards [hsampleae, ae_summable_samples hα hβ hgap hαβ x,
      rationalPositiveBaseFiberJoint_slice_ae hα hβ hgap hαβ x,
      (ae_restrict_mem measurableSet_Ioc : ∀ᵐ s ∂(volume.restrict
        (Set.Ioc (0 : ℝ) (rationalZakEta α p q))), s ∈ Set.Ioc (0 : ℝ) (rationalZakEta α p q))]
      with s hsampleeq hc hslice_base hsmem
    have hslice : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹)),
        ∀ a : Fin p,
          rationalPositiveBaseFiberJoint hα hβ hgap hαβ x
            (s, ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) =
          rationalPositiveBaseFrequencyFiber hα hβ hgap hαβ x s
            (ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q) := by
      rw [ae_all_iff]
      intro a
      refine ae_eq_comp_add_right hslice_base (fun ξ hξ => ?_)
      rw [rationalZakEta_inv_eq_p_div_gamma hα hβ hgap hαβ]
      refine ⟨by
        have hnonneg : 0 ≤ ((a : ℕ) : ℝ) / rationalZakGamma α q := by positivity
        linarith [hξ.1], ?_⟩
      have h1 : ξ ≤ (rationalZakGamma α q)⁻¹ := hξ.2
      have ha_le : (1 : ℝ) + ((a : ℕ) : ℝ) ≤ (p : ℝ) := by
        have hlt : (a : ℕ) + 1 ≤ p := a.2
        have : ((a : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hlt
        linarith
      have hinv : (rationalZakGamma α q)⁻¹ = 1 / rationalZakGamma α q := inv_eq_one_div _
      calc ξ + ((a : ℕ) : ℝ) / rationalZakGamma α q
          ≤ 1 / rationalZakGamma α q + ((a : ℕ) : ℝ) / rationalZakGamma α q := by
            rw [← hinv]; linarith [h1]
        _ = (1 + ((a : ℕ) : ℝ)) / rationalZakGamma α q := by rw [← add_div]
        _ ≤ (p : ℝ) / rationalZakGamma α q := by gcongr
    rw [ennreal_msum_sq_eq_matrix_of_hyps hτ hα hβ hpq_coprime hgap hαβ x hφ_cs hsmem
      hsampleeq (fun s' => summable_norm_compactSupport_samples hγpos hφ_cs
        (s + rationalZakEta α p q * ((s' : ℕ) : ℝ))) hc hslice]
    exact Finset.sum_congr rfl (fun t _ => by
      rw [intervalIntegral.integral_of_le (inv_pos.mpr hγpos).le])
  rw [lintegral_congr_ae hae, lintegral_finsetSum' _ (fun t _ =>
    ((matrixComponent_marginal_integrableOn hτ hα hβ hpq_coprime hgap hαβ x t).const_mul
      (rationalZakGamma α q)).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  have hmarg : ∀ t : Fin q,
      (∫⁻ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q), ENNReal.ofReal (rationalZakGamma α q *
        ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2))
      = ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ) (rationalZakEta α p q), rationalZakGamma α q *
        ∫ ξ in Set.Ioc (0 : ℝ) (rationalZakGamma α q)⁻¹,
          ‖(generalizedRationalZakMatrix τ α p q (s, ξ) *ᵥ
            rationalPositiveGammaFiberField hα hβ hpq_coprime hgap hαβ x (s, ξ)) t‖ ^ 2) := by
    intro t
    rw [ofReal_integral_eq_lintegral_ofReal
      ((matrixComponent_marginal_integrableOn hτ hα hβ hpq_coprime hgap hαβ x t).const_mul _)
      (Filter.Eventually.of_forall (fun s => mul_nonneg hγpos.le (integral_nonneg
        (fun ξ => sq_nonneg _))))]
  simp_rw [hmarg]
  rw [Finset.mul_sum]
  simp_rw [← ENNReal.ofReal_mul hβ0]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg hβ0 (integral_nonneg
      (fun s => mul_nonneg hγpos.le (integral_nonneg (fun ξ => sq_nonneg _)))))]
  exact congrArg ENNReal.ofReal (iterated_eq_euclidean hτ hα hβ hpq_coprime hgap hαβ x)

/-- **The corrected coefficient identity on the compact-support class.**  For `x` with a
continuous compact-support representative `φ`, `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) x` equals the corrected
(Euclidean) matrix-energy integral.  Extracted from the ENNReal identity: its finiteness
forces the Gabor Bessel summability, and `ENNReal.toReal` peels off the `ofReal`. -/
lemma productCoeffEnergy_eq_euclidean_of_compactSupport {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    (x : Lp ℂ 2 (volume : Measure ℝ)) (φ : C(ℝ, ℂ)) (hφ_cs : HasCompactSupport ⇑φ)
    (hxφ : (x : ℝ → ℂ) =ᵐ[volume] ⇑φ) :
    generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β x
      = gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x := by
  have hkey := productCoeffEnergy_ennreal_eq_euclidean
    (τ := τ) (hτ := hτ) hα hβ hpq_coprime hgap hαβ x φ hφ_cs hxφ
  have hRHSnn : 0 ≤ gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x := by
    refine integral_nonneg (fun z => ?_)
    exact mul_nonneg (mul_nonneg (rationalZakEta_pos hα hβ hgap hαβ).le
      (rationalZakGamma_pos hα (q_pos_of_gap hgap)).le)
      (Finset.sum_nonneg (fun t _ => sq_nonneg _))
  have hsum : Summable (fun mn : ℤ × ℤ =>
      ‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2) := by
    have hne : (∑' mn : ℤ × ℤ, ENNReal.ofReal
        (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2)) ≠ ⊤ := by
      rw [hkey]; exact ENNReal.ofReal_ne_top
    have hNN : Summable (fun mn : ℤ × ℤ =>
        (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2).toNNReal) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hne
    exact (NNReal.summable_coe.mpr hNN).congr (fun mn => Real.coe_toNNReal _ (sq_nonneg _))
  unfold generalizedProductCoeffEnergy
  rw [← ENNReal.toReal_ofReal (tsum_nonneg (fun mn => sq_nonneg _)),
    ENNReal.ofReal_tsum_of_nonneg (fun mn => sq_nonneg _) hsum, hkey,
    ENNReal.toReal_ofReal hRHSnn]

/-- Obligation (dense identity, Phase A+B). There is a dense set of inputs — the
compact-support class — on which the coefficient identity holds by the explicit
Zibulski–Zeevi calculation (B1 modulation Parseval, B2 reindex `m=qℓ−b`,
B3 Parseval in `ξ`, B4 match to the finite row-change matrix energy). -/
theorem exists_dense_eqOn
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ D : Set (Lp ℂ 2 (volume : Measure ℝ)),
      Dense D ∧
      Set.EqOn (generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β)
        (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ) D := by
  refine ⟨{x | ∃ φ : ℝ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧
      (x : ℝ → ℂ) =ᵐ[volume] φ}, ?_, ?_⟩
  · refine Metric.dense_iff.mpr (fun x r hr => ?_)
    obtain ⟨g, ⟨φ, hcont, hcs, hgφ⟩, hclose⟩ :=
      exists_continuous_compactSupport_Lp_approx x hr
    exact ⟨g, by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hclose,
      φ, hcont, hcs, hgφ⟩
  · intro x hx
    obtain ⟨φ, hcont, hcs, hxφ⟩ := hx
    exact productCoeffEnergy_eq_euclidean_of_compactSupport hα hβ hpq_coprime hgap hαβ x
      ⟨φ, hcont⟩ hcs hxφ

/-- **Gabor Bessel bound (all `x`), Fatou route.**  The coefficient energy is summable
and `≤ C‖x‖²` for a fixed `C` — obtained *without* frame theory: the ENNReal coefficient
energy is lower-semicontinuous and, on the dense compact-support class, equals
`ofReal(gammaMatrixEuclidean) ≤ ofReal(C‖x‖²)`; lower-semicontinuity extends the bound to
all `x`, and finiteness gives summability. -/
lemma productCoeffEnergy_bessel {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      Summable (fun mn : ℤ × ℤ =>
        ‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2) ∧
      (∑' mn : ℤ × ℤ, ‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2)
        ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := gammaMatrixEuclideanEnergyIntegral_le hτ hα hβ hpq_coprime hgap hαβ
  set D : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
    {x | ∃ φ : ℝ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ (x : ℝ → ℂ) =ᵐ[volume] φ} with hDdef
  have hDdense : Dense D := by
    refine Metric.dense_iff.mpr (fun x r hr => ?_)
    obtain ⟨g, ⟨φ, hcont, hcs, hgφ⟩, hclose⟩ :=
      exists_continuous_compactSupport_Lp_approx x hr
    exact ⟨g, by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hclose,
      φ, hcont, hcs, hgφ⟩
  have hlsc := productCoeffEnergy_ennreal_lowerSemicontinuous
    (τ := τ) (hτ := hτ) α β
  have hgcont : Continuous (fun y : Lp ℂ 2 (volume : Measure ℝ) =>
      ENNReal.ofReal (C * ‖y‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  refine ⟨C, hC0, fun x => ?_⟩
  have hEbound : (∑' mn : ℤ × ℤ, ENNReal.ofReal
      (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2))
      ≤ ENNReal.ofReal (C * ‖x‖ ^ 2) := by
    obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp (hDdense x)
    by_contra hcon
    push_neg at hcon
    obtain ⟨z, hz1, hz2⟩ := exists_between hcon
    have hzle : z ≤ ENNReal.ofReal (C * ‖x‖ ^ 2) := by
      refine ge_of_tendsto ((hgcont.tendsto x).comp hu_tend) ?_
      filter_upwards [hu_tend.eventually (hlsc x z hz2)] with n hn
      obtain ⟨φ, hcont', hcs, hyφ⟩ := hu_mem n
      refine (lt_of_lt_of_le hn ?_).le
      calc (∑' mn : ℤ × ℤ, ENNReal.ofReal
              (‖inner ℂ (u n) (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2))
          = ENNReal.ofReal
              (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ (u n)) :=
            productCoeffEnergy_ennreal_eq_euclidean hα hβ hpq_coprime hgap hαβ (u n)
              ⟨φ, hcont'⟩ hcs hyφ
        _ ≤ ENNReal.ofReal (C * ‖u n‖ ^ 2) := ENNReal.ofReal_le_ofReal (hC (u n))
    exact absurd hzle (not_le.mpr hz1)
  have hne : (∑' mn : ℤ × ℤ, ENNReal.ofReal
      (‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEbound
  have hsum : Summable (fun mn : ℤ × ℤ =>
      ‖inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)‖ ^ 2) :=
    (NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hne)).congr
      (fun mn => Real.coe_toNNReal _ (sq_nonneg _))
  refine ⟨hsum, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ C * ‖x‖ ^ 2),
    ENNReal.ofReal_tsum_of_nonneg (fun mn => sq_nonneg _) hsum]
  exact hEbound

/-- **Obligation 1 — LHS continuity.**  `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ)` is continuous.  The Gabor
analysis operator `A x = (⟨x,g_{mn}⟩)_{mn}` lands in `ℓ²(ℤ²)` (Bessel bound), is
`√C`-Lipschitz (antilinear + the bound, `‖A x - A y‖ = ‖A(x−y)‖ ≤ √C‖x−y‖`), hence
continuous, and `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) x = ‖A x‖²`. -/
theorem productCoeffEnergy_continuous {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    Continuous (generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β) := by
  obtain ⟨C, hC0, hbessel⟩ := productCoeffEnergy_bessel hα hβ hpq_coprime hgap hαβ
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hpow : ∀ y : ℝ, y ^ (2 : ℝ≥0∞).toReal = y ^ 2 := fun y => by
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmem : ∀ x : Lp ℂ 2 (volume : Measure ℝ),
      Memℓp (fun mn : ℤ × ℤ => inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2)) 2 := by
    intro x
    rw [memℓp_gen_iff h2]
    exact (hbessel x).1.congr (fun mn => (hpow _).symm)
  set A : Lp ℂ 2 (volume : Measure ℝ) → lp (fun _ : ℤ × ℤ => ℂ) 2 :=
    fun x => ⟨fun mn => inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2), hmem x⟩ with hAdef
  have hAcoe : ∀ (x : Lp ℂ 2 (volume : Measure ℝ)) (mn : ℤ × ℤ),
      (A x : ℤ × ℤ → ℂ) mn
        = inner ℂ x (generalizedH1ElementLp τ hτ α β mn.1 mn.2) :=
    fun x mn => rfl
  have hnormsq : ∀ x, ‖A x‖ ^ 2 = generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β x := by
    intro x
    have hn := lp.norm_rpow_eq_tsum h2 (A x)
    rw [hpow] at hn
    rw [hn]
    unfold generalizedProductCoeffEnergy
    exact tsum_congr (fun mn => by rw [hAcoe x mn, hpow])
  have hAlip : ∀ x y, ‖A x - A y‖ ≤ Real.sqrt C * ‖x - y‖ := by
    intro x y
    have hn := lp.norm_rpow_eq_tsum h2 (A x - A y)
    rw [hpow] at hn
    have hval : (∑' mn : ℤ × ℤ, ‖((A x - A y : lp (fun _ : ℤ × ℤ => ℂ) 2) :
          ℤ × ℤ → ℂ) mn‖ ^ (2 : ℝ≥0∞).toReal)
        = generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β (x - y) := by
      unfold generalizedProductCoeffEnergy
      refine tsum_congr (fun mn => ?_)
      rw [lp.coeFn_sub, Pi.sub_apply, hAcoe x mn, hAcoe y mn, ← inner_sub_left, hpow]
    have h1 : ‖A x - A y‖ ^ 2 ≤ C * ‖x - y‖ ^ 2 := by
      rw [hn, hval]; exact (hbessel (x - y)).2
    calc ‖A x - A y‖ = Real.sqrt (‖A x - A y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C * ‖x - y‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt C * ‖x - y‖ := by
          rw [Real.sqrt_mul hC0, Real.sqrt_sq (norm_nonneg _)]
  have hAcont : Continuous A :=
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.sqrt C)) (fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
      exact hAlip x y)).continuous
  exact (hAcont.norm.pow 2).congr (fun x => hnormsq x)

/-- **Coefficient identity, from the pieces.** Dense agreement plus continuity of both
sides forces global agreement (`Continuous.ext_on`).  This is the *Euclidean* form of the
identity: the naive sup-norm form fails for `q ≥ 2` (see
`gammaMatrixEnergyIntegral_le_euclidean`), so the inner-product (Euclidean) energy is the
correct one. -/
theorem rationalPositiveGammaMatrix_coeff_identity_euclidean_of_pieces
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ))
    {D : Set (Lp ℂ 2 (volume : Measure ℝ))}
    (hdense : Dense D)
    (hLHS : Continuous (generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β))
    (hRHS : Continuous (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ))
    (heq : Set.EqOn (generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β)
      (gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ) D) :
    ∀ x : Lp ℂ 2 (volume : Measure ℝ), generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β x =
      gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x :=
  fun x => congrFun (Continuous.ext_on hdense hLHS hRHS heq) x

/-- **The gamma-fiber coefficient identity.**  `generalizedProductCoeffEnergy (τ := τ) (hτ := hτ)` equals the
inner-product (Euclidean) matrix-energy integral.  The naive sup-norm form of this identity
fails for `q ≥ 2` (`gammaMatrixEnergyIntegral_le_euclidean`); the Euclidean form proved here
is the correct one, assembled from `productCoeffEnergy_continuous` and `exists_dense_eqOn`. -/
theorem rationalPositiveGammaMatrix_coeff_identity
    {α β : ℝ} {p q : ℕ} [NeZero q]
    (hα : 0 < α) (hβ : 0 < β) (hpq_coprime : Nat.Coprime p q)
    (hgap : q ≥ p + 2) (hαβ : α * β = (p : ℝ) / (q : ℝ)) :
    (∀ x : Lp ℂ 2 (volume : Measure ℝ), generalizedProductCoeffEnergy (τ := τ) (hτ := hτ) α β x =
      gammaMatrixEuclideanEnergyIntegral (τ := τ) hα hβ hpq_coprime hgap hαβ x) := by
  obtain ⟨D, hdense, heq⟩ := exists_dense_eqOn hα hβ hpq_coprime hgap hαβ
  exact rationalPositiveGammaMatrix_coeff_identity_euclidean_of_pieces
    hα hβ hpq_coprime hgap hαβ hdense
    (productCoeffEnergy_continuous hα hβ hpq_coprime hgap hαβ)
    (gammaMatrixEuclideanEnergyIntegral_continuous hτ hα hβ hpq_coprime hgap hαβ)
    heq

end LyubarskiiNes.GeneralLattice.GeneralizedCriterion
