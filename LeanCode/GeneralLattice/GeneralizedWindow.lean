import LeanCode.GeneralLattice.Definitions
import LeanCode.RationalDensity.RationalPositive.GammaCoeffWork

open MeasureTheory

namespace LyubarskiiNes.GeneralLattice

/-- The metaplectic orbit model for the first Hermite window.  For
`Im τ > 0`, this is a linearly weighted decaying complex Gaussian. -/
noncomputable def generalizedH1 (τ : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2)

lemma norm_generalizedH1_sq (τ : ℂ) (t : ℝ) :
    ‖generalizedH1 τ t‖ ^ 2 =
      t ^ (2 : ℕ) * Real.exp (-(2 * Real.pi * τ.im) * t ^ 2) := by
  unfold generalizedH1
  rw [Complex.norm_mul, Complex.norm_exp, mul_pow]
  have hre :
      ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2).re =
        -Real.pi * τ.im * t ^ 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hre, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show Real.exp (-Real.pi * τ.im * t ^ 2) ^ 2 =
      Real.exp (-Real.pi * τ.im * t ^ 2) *
        Real.exp (-Real.pi * τ.im * t ^ 2) by ring]
  rw [← Real.exp_add]
  ring_nf

lemma norm_generalizedH1 (τ : ℂ) (t : ℝ) :
    ‖generalizedH1 τ t‖ =
      |t| * Real.exp (-Real.pi * τ.im * t ^ 2) := by
  unfold generalizedH1
  rw [Complex.norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre :
      ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2).re =
        -Real.pi * τ.im * t ^ 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hre]

private lemma norm_generalizedH1_eq_rescaled_gaussian
    {τ : ℂ} (hτ : 0 < τ.im) (t : ℝ) :
    ‖generalizedH1 τ t‖ =
      (Real.sqrt τ.im)⁻¹ *
        ‖LyubarskiiNes.RationalDensity.gaussianH1C (Real.sqrt τ.im * t)‖ := by
  have hs : 0 < Real.sqrt τ.im := Real.sqrt_pos.2 hτ
  have hs0 : Real.sqrt τ.im ≠ 0 := ne_of_gt hs
  rw [norm_generalizedH1,
    LyubarskiiNes.RationalDensity.norm_gaussianH1C]
  rw [abs_mul, abs_of_pos hs, mul_pow, Real.sq_sqrt hτ.le]
  field_simp [hs0]

/-- Generalized first-Hermite samples on every positive arithmetic scale are
square summable. -/
lemma summable_sq_norm_generalizedH1_samples
    {τ : ℂ} (hτ : 0 < τ.im) (γ : ℝ) (hγ : 0 < γ) (x : ℝ) :
    Summable fun k : ℤ => ‖generalizedH1 τ (x - γ * (k : ℝ))‖ ^ 2 := by
  let d : ℝ := Real.sqrt τ.im
  have hd : 0 < d := Real.sqrt_pos.2 hτ
  have hbase :=
    LyubarskiiNes.RationalDensity.summable_sq_norm_gaussianH1C_samples
      (d * γ) (mul_pos hd hγ) (d * x)
  have hscaled := hbase.mul_left (d⁻¹ ^ 2)
  refine hscaled.congr (fun k ↦ ?_)
  rw [norm_generalizedH1_eq_rescaled_gaussian hτ]
  rw [mul_pow]
  dsimp [d]
  congr 2
  congr 1
  ring

/-- Generalized first-Hermite samples on every positive arithmetic scale are
absolutely summable. -/
lemma summable_norm_generalizedH1_samples
    {τ : ℂ} (hτ : 0 < τ.im) (γ : ℝ) (hγ : 0 < γ) (x : ℝ) :
    Summable fun k : ℤ => ‖generalizedH1 τ (x - γ * (k : ℝ))‖ := by
  let d : ℝ := Real.sqrt τ.im
  have hd : 0 < d := Real.sqrt_pos.2 hτ
  have hbase :=
    LyubarskiiNes.RationalDensity.summable_norm_gaussianH1C_samples
      (d * γ) (mul_pos hd hγ) (d * x)
  have hscaled := hbase.mul_left d⁻¹
  refine hscaled.congr (fun k ↦ ?_)
  rw [norm_generalizedH1_eq_rescaled_gaussian hτ]
  dsimp [d]
  congr 1
  ring

/-- A generalized first-Hermite Gaussian lies in `L²` whenever its parameter
is in the upper half-plane. -/
theorem memLp_generalizedH1 {τ : ℂ} (hτ : 0 < τ.im) :
    MemLp (generalizedH1 τ) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (generalizedH1 τ) (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    unfold generalizedH1
    continuity
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have hb : 0 < 2 * Real.pi * τ.im := by positivity
  have hint : Integrable (fun t : ℝ => t ^ (2 : ℕ) *
      Real.exp (-(2 * Real.pi * τ.im) * t ^ 2)) (volume : Measure ℝ) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq
        (b := 2 * Real.pi * τ.im) (s := (2 : ℝ)) hb
        (by norm_num : (-1 : ℝ) < 2))
  exact hint.congr (Filter.Eventually.of_forall fun t =>
    (norm_generalizedH1_sq τ t).symm)

/-- A generalized first-Hermite Gaussian as an element of `L²(ℝ)`. -/
noncomputable def generalizedH1Lp (τ : ℂ) (hτ : 0 < τ.im) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_generalizedH1 hτ).toLp

/-- The translated and modulated generalized first-Hermite atom.  This is the
window family which occurs after the Iwasawa/metaplectic reduction of an
arbitrary lattice to `(p/q)ℤ × ℤ`. -/
noncomputable def generalizedH1Element
    (τ : ℂ) (α β : ℝ) (m n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) * (t : ℂ)) *
    generalizedH1 τ (t - α * (m : ℝ))

private lemma norm_generalizedH1Element_sq
    (τ : ℂ) (α β : ℝ) (m n : ℤ) (t : ℝ) :
    ‖generalizedH1Element τ α β m n t‖ ^ 2 =
      ‖generalizedH1 τ (t - α * (m : ℝ))‖ ^ 2 := by
  unfold generalizedH1Element
  rw [norm_mul]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) * (t : ℂ) =
        ((2 * Real.pi * β * (n : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Every atom of the generalized first-Hermite Gabor family is in `L²`. -/
theorem memLp_generalizedH1Element
    {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) (m n : ℤ) :
    MemLp (generalizedH1Element τ α β m n) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (generalizedH1Element τ α β m n)
      (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    unfold generalizedH1Element generalizedH1
    continuity
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have hbase : Integrable (fun t : ℝ => ‖generalizedH1 τ t‖ ^ 2)
      (volume : Measure ℝ) := by
    have hg := memLp_generalizedH1 hτ
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hg.1] at hg
    exact hg
  have hshift : Integrable
      ((fun t : ℝ => ‖generalizedH1 τ t‖ ^ 2) ∘
        fun t : ℝ => t - α * (m : ℝ)) (volume : Measure ℝ) :=
    ((MeasureTheory.measurePreserving_sub_right (volume : Measure ℝ)
      (α * (m : ℝ))).integrable_comp hbase.aestronglyMeasurable).2 hbase
  exact hshift.congr (Filter.Eventually.of_forall fun t => by
    simpa [Function.comp_def] using
      (norm_generalizedH1Element_sq τ α β m n t).symm)

/-- A generalized first-Hermite Gabor atom as an element of `L²(ℝ)`. -/
noncomputable def generalizedH1ElementLp
    (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) (m n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_generalizedH1Element hτ α β m n).toLp

/-- Frame predicate for the generalized window on a separable lattice. -/
def IsGeneralizedGaborFrame
    (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ f : Lp ℂ 2 (volume : Measure ℝ),
    A * ‖f‖ ^ 2 ≤
        ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ f (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2
      ∧
        ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ f (generalizedH1ElementLp τ hτ α β m n)‖ ^ 2
        ≤ B * ‖f‖ ^ 2

/-- A generalized first-Hermite atom at an arbitrary lattice point. -/
noncomputable def generalizedH1LatticeElement
    (τ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (latticeFrequency M m n : ℂ) * (t : ℂ)) *
    generalizedH1 τ (t - latticeTime M m n)

lemma generalizedH1LatticeElement_eq_element
    (τ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    generalizedH1LatticeElement τ M m n =
      generalizedH1Element τ (latticeTime M m n) (latticeFrequency M m n) 1 1 := by
  funext t
  simp [generalizedH1LatticeElement, generalizedH1Element]

theorem memLp_generalizedH1LatticeElement
    {τ : ℂ} (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    MemLp (generalizedH1LatticeElement τ M m n) 2 (volume : Measure ℝ) := by
  rw [generalizedH1LatticeElement_eq_element]
  exact memLp_generalizedH1Element hτ _ _ 1 1

noncomputable def generalizedH1LatticeElementLp
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_generalizedH1LatticeElement hτ M m n).toLp

/-- Frame predicate for a generalized first-Hermite window on an arbitrary
matrix lattice. -/
def IsGeneralizedGaborFrameForLattice
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ f : Lp ℂ 2 (volume : Measure ℝ),
    A * ‖f‖ ^ 2 ≤
        ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ f (generalizedH1LatticeElementLp τ hτ M m n)‖ ^ 2
      ∧
        ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ f (generalizedH1LatticeElementLp τ hτ M m n)‖ ^ 2
        ≤ B * ‖f‖ ^ 2

lemma generalizedH1LatticeElement_separable
    (τ : ℂ) (α β : ℝ) (m n : ℤ) :
    generalizedH1LatticeElement τ (separableLatticeMatrix α β) m n =
      generalizedH1Element τ α β m n := by
  funext t
  simp only [generalizedH1LatticeElement, generalizedH1Element,
    latticeFrequency_separableLatticeMatrix, latticeTime_separableLatticeMatrix]
  congr 2 <;> push_cast <;> ring

lemma generalizedH1LatticeElementLp_separable
    (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) (m n : ℤ) :
    generalizedH1LatticeElementLp τ hτ (separableLatticeMatrix α β) m n =
      generalizedH1ElementLp τ hτ α β m n := by
  unfold generalizedH1LatticeElementLp generalizedH1ElementLp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t =>
    congrFun (generalizedH1LatticeElement_separable τ α β m n) t

theorem isGeneralizedGaborFrameForLattice_separable_iff
    (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) :
    IsGeneralizedGaborFrameForLattice τ hτ (separableLatticeMatrix α β) ↔
      IsGeneralizedGaborFrame τ hτ α β := by
  simp only [IsGeneralizedGaborFrameForLattice, IsGeneralizedGaborFrame,
    generalizedH1LatticeElementLp_separable]

/-- The original first Hermite window is the parameter `τ = i`. -/
lemma generalizedH1_I :
    generalizedH1 Complex.I =
      LyubarskiiNes.RationalDensity.gaussianH1C := by
  funext t
  unfold generalizedH1 LyubarskiiNes.RationalDensity.gaussianH1C
    LyubarskiiNes.RationalDensity.gaussianH1
  have harg :
      (Real.pi : ℂ) * Complex.I * Complex.I * (t : ℂ) ^ 2 =
        ((-Real.pi * t ^ 2 : ℝ) : ℂ) := by
    calc
      (Real.pi : ℂ) * Complex.I * Complex.I * (t : ℂ) ^ 2 =
          (Real.pi : ℂ) * (Complex.I * Complex.I) * (t : ℂ) ^ 2 := by ring
      _ = (Real.pi : ℂ) * (-1) * (t : ℂ) ^ 2 := by rw [Complex.I_mul_I]
      _ = ((-Real.pi * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  rfl

lemma generalizedH1Element_I (α β : ℝ) (m n : ℤ) :
    generalizedH1Element Complex.I α β m n =
      LyubarskiiNes.h1_element α β m n := by
  funext t
  unfold generalizedH1Element
  rw [show generalizedH1 Complex.I (t - α * (m : ℝ)) =
      LyubarskiiNes.RationalDensity.gaussianH1C (t - α * (m : ℝ)) from
    congrFun generalizedH1_I _]
  unfold LyubarskiiNes.h1_element
    LyubarskiiNes.RationalDensity.gaussianH1C
    LyubarskiiNes.RationalDensity.gaussianH1
  push_cast
  ring

lemma generalizedH1ElementLp_I (α β : ℝ) (m n : ℤ) :
    generalizedH1ElementLp Complex.I (by norm_num) α β m n =
      LyubarskiiNes.h1_element_Lp α β m n := by
  unfold generalizedH1ElementLp LyubarskiiNes.h1_element_Lp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t => congrFun (generalizedH1Element_I α β m n) t

/-- At `τ = i`, the generalized frame predicate is exactly the old separable
frame predicate. -/
theorem isGeneralizedGaborFrame_I_iff (α β : ℝ) :
    IsGeneralizedGaborFrame Complex.I (by norm_num) α β ↔
      LyubarskiiNes.IsGaborFrame α β := by
  simp only [IsGeneralizedGaborFrame, LyubarskiiNes.IsGaborFrame,
    generalizedH1ElementLp_I]

/-- Pointwise multiplication by the quadratic phase corresponding to a lower
symplectic shear. -/
noncomputable def chirp (η : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2) * f t

/-- Chirping stays inside the generalized first-Hermite family. -/
lemma chirp_generalizedH1 (η : ℝ) (τ : ℂ) :
    chirp η (generalizedH1 τ) = generalizedH1 (τ + η) := by
  funext t
  unfold chirp generalizedH1
  calc
    Complex.exp ((Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2) *
          ((t : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2)) =
        (t : ℂ) *
          (Complex.exp ((Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2) *
            Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2)) := by ring
    _ = (t : ℂ) * Complex.exp
          (((Real.pi : ℂ) * Complex.I * (η : ℂ) * (t : ℂ) ^ 2) +
            ((Real.pi : ℂ) * Complex.I * τ * (t : ℂ) ^ 2)) := by
          rw [Complex.exp_add]
    _ = (t : ℂ) * Complex.exp
          ((Real.pi : ℂ) * Complex.I * (τ + η) * (t : ℂ) ^ 2) := by
          congr 2
          ring

end LyubarskiiNes.GeneralLattice
