import LeanCode.GeneralLattice.GeneralizedWindow

open MeasureTheory
open scoped BigOperators

namespace LyubarskiiNes.GeneralLattice

/-- The frame inequalities for a doubly indexed family.  Keeping the two
integer indices explicit makes this definition definitionally compatible with
the existing separable development. -/
def IsFrameFamily
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℤ → ℤ → H) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ f : H,
    A * ‖f‖ ^ 2 ≤
        ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2
      ∧
        ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2
        ≤ B * ‖f‖ ^ 2

lemma isGaborFrameForLattice_iff_isFrameFamily
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGaborFrameForLattice M ↔ IsFrameFamily (h1LatticeElementLp M) := by
  rfl

/-- Frame inequalities depend only on the absolute values of all analysis
coefficients.  This absorbs the harmless point-dependent phases in
metaplectic covariance formulas. -/
theorem isFrameFamily_congr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {v w : ℤ → ℤ → H}
    (hcoeff : ∀ (f : H) (m n : ℤ),
      ‖inner ℂ f (v m n)‖ = ‖inner ℂ f (w m n)‖) :
    IsFrameFamily v ↔ IsFrameFamily w := by
  simp only [IsFrameFamily]
  constructor
  · rintro ⟨A, B, hA, hAB, h⟩
    refine ⟨A, B, hA, hAB, ?_⟩
    intro f
    simpa only [hcoeff f] using h f
  · rintro ⟨A, B, hA, hAB, h⟩
    refine ⟨A, B, hA, hAB, ?_⟩
    intro f
    simpa only [hcoeff f] using h f

/-- A unitary operator transports a frame family to a frame family, with the
same frame bounds. -/
theorem isFrameFamily_linearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (v : ℤ → ℤ → H) :
    IsFrameFamily (fun m n ↦ U (v m n)) ↔ IsFrameFamily v := by
  constructor
  · rintro ⟨A, B, hA, hAB, h⟩
    refine ⟨A, B, hA, hAB, ?_⟩
    intro f
    have hf := h (U f)
    simpa only [U.norm_map, U.inner_map_map] using hf
  · rintro ⟨A, B, hA, hAB, h⟩
    refine ⟨A, B, hA, hAB, ?_⟩
    intro f
    have hf := h (U.symm f)
    have hinner (m n : ℤ) :
        inner ℂ f (U (v m n)) = inner ℂ (U.symm f) (v m n) := by
      calc
        inner ℂ f (U (v m n)) =
            inner ℂ (U (U.symm f)) (U (v m n)) := by
              rw [U.apply_symm_apply]
        _ = inner ℂ (U.symm f) (v m n) := U.inner_map_map _ _
    simpa only [U.symm.norm_map, hinner] using hf

/-- Reindexing either integer coordinate by a bijection does not change the
frame property. -/
theorem isFrameFamily_reindex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℤ → ℤ → H) (e₁ e₂ : ℤ ≃ ℤ) :
    IsFrameFamily (fun m n ↦ v (e₁ m) (e₂ n)) ↔ IsFrameFamily v := by
  have hsum : ∀ f : H,
      (∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v (e₁ m) (e₂ n))‖ ^ 2) =
        ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 := by
    intro f
    calc
      (∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v (e₁ m) (e₂ n))‖ ^ 2) =
          ∑' m : ℤ, ∑' n : ℤ, ‖inner ℂ f (v (e₁ m) n)‖ ^ 2 := by
            apply tsum_congr
            intro m
            exact Equiv.tsum_eq e₂ (fun n : ℤ => ‖inner ℂ f (v (e₁ m) n)‖ ^ 2)
      _ = ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 :=
        Equiv.tsum_eq e₁ (fun m : ℤ => ∑' n : ℤ, ‖inner ℂ f (v m n)‖ ^ 2)
  simp only [IsFrameFamily]
  constructor <;> rintro ⟨A, B, hA, hAB, h⟩ <;>
    exact ⟨A, B, hA, hAB, fun f => by simpa only [hsum f] using h f⟩

private lemma isFrameFamily_smul_imp
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℤ → ℤ → H) (c : ℂ) (hc : c ≠ 0) :
    IsFrameFamily v → IsFrameFamily (fun m n ↦ c • v m n) := by
  rintro ⟨A, B, hA, hAB, hframe⟩
  let c₂ : ℝ := ‖c‖ ^ 2
  have hc₂ : 0 < c₂ := sq_pos_of_pos (norm_pos_iff.mpr hc)
  refine ⟨c₂ * A, c₂ * B, mul_pos hc₂ hA,
    mul_le_mul_of_nonneg_left hAB hc₂.le, ?_⟩
  intro f
  have henergy :
      (∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (c • v m n)‖ ^ 2) =
        c₂ * ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 := by
    calc
      (∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (c • v m n)‖ ^ 2) =
          ∑' (m : ℤ) (n : ℤ), c₂ * ‖inner ℂ f (v m n)‖ ^ 2 := by
            apply tsum_congr
            intro m
            apply tsum_congr
            intro n
            simp [c₂, norm_mul, mul_pow]
      _ = ∑' m : ℤ, c₂ * ∑' n : ℤ, ‖inner ℂ f (v m n)‖ ^ 2 := by
            apply tsum_congr
            intro m
            exact tsum_mul_left
      _ = c₂ * ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 := tsum_mul_left
  rw [henergy]
  constructor
  · calc
      (c₂ * A) * ‖f‖ ^ 2 = c₂ * (A * ‖f‖ ^ 2) := by ring
      _ ≤ c₂ * ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hframe f).1 hc₂.le
  · calc
      c₂ * ∑' (m : ℤ) (n : ℤ), ‖inner ℂ f (v m n)‖ ^ 2 ≤
          c₂ * (B * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left (hframe f).2 hc₂.le
      _ = (c₂ * B) * ‖f‖ ^ 2 := by ring

/-- Multiplying every vector of a frame by the same nonzero scalar preserves
the frame property. -/
theorem isFrameFamily_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℤ → ℤ → H) (c : ℂ) (hc : c ≠ 0) :
    IsFrameFamily (fun m n ↦ c • v m n) ↔ IsFrameFamily v := by
  constructor
  · intro h
    have hinv := isFrameFamily_smul_imp (fun m n ↦ c • v m n) c⁻¹ (inv_ne_zero hc) h
    simpa [smul_smul, hc] using hinv
  · exact isFrameFamily_smul_imp v c hc

lemma isGeneralizedGaborFrame_iff_isFrameFamily
    (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) :
    IsGeneralizedGaborFrame τ hτ α β ↔
      IsFrameFamily (generalizedH1ElementLp τ hτ α β) := by
  rfl

lemma isGeneralizedGaborFrameForLattice_iff_isFrameFamily
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice τ hτ M ↔
      IsFrameFamily (generalizedH1LatticeElementLp τ hτ M) := by
  rfl

end LyubarskiiNes.GeneralLattice
