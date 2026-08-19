import LeanCode.GeneralLattice.FourierMetaplectic
import LeanCode.GeneralLattice.GeneralizedFrame

open MeasureTheory
open scoped Matrix BigOperators

namespace LyubarskiiNes.GeneralLattice

@[simp] lemma latticeTime_neg_matrix
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeTime (-M) m n = latticeTime M (-m) (-n) := by
  simp [latticeTime]

@[simp] lemma latticeFrequency_neg_matrix
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeFrequency (-M) m n = latticeFrequency M (-m) (-n) := by
  simp [latticeFrequency]

lemma generalizedH1LatticeElement_neg_matrix
    (τ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    generalizedH1LatticeElement τ (-M) m n =
      generalizedH1LatticeElement τ M (-m) (-n) := by
  funext t
  simp [generalizedH1LatticeElement]

lemma generalizedH1LatticeElementLp_neg_matrix
    (τ : ℂ) (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    generalizedH1LatticeElementLp τ hτ (-M) m n =
      generalizedH1LatticeElementLp τ hτ M (-m) (-n) := by
  unfold generalizedH1LatticeElementLp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t =>
    congrFun (generalizedH1LatticeElement_neg_matrix τ M m n) t

/-- Multiplication of the lattice by `-I` only reindexes both integer
coordinates. -/
theorem isGeneralizedGaborFrameForLattice_neg_iff
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice τ hτ (-M) ↔
      IsGeneralizedGaborFrameForLattice τ hτ M := by
  rw [isGeneralizedGaborFrameForLattice_iff_isFrameFamily,
    isGeneralizedGaborFrameForLattice_iff_isFrameFamily]
  have hfamily : generalizedH1LatticeElementLp τ hτ (-M) =
      fun m n => generalizedH1LatticeElementLp τ hτ M (-m) (-n) := by
    funext m n
    exact generalizedH1LatticeElementLp_neg_matrix τ hτ M m n
  rw [hfamily]
  simpa using (isFrameFamily_reindex
    (generalizedH1LatticeElementLp τ hτ M) (Equiv.neg ℤ) (Equiv.neg ℤ))

lemma generalizedH1LatticeElement_I
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    generalizedH1LatticeElement Complex.I M m n = h1LatticeElement M m n := by
  funext t
  unfold generalizedH1LatticeElement h1LatticeElement
  rw [show generalizedH1 Complex.I (t - latticeTime M m n) =
      LyubarskiiNes.RationalDensity.gaussianH1C (t - latticeTime M m n) from
    congrFun generalizedH1_I _]
  unfold LyubarskiiNes.RationalDensity.gaussianH1C
    LyubarskiiNes.RationalDensity.gaussianH1
  push_cast
  ring

lemma generalizedH1LatticeElementLp_I
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    generalizedH1LatticeElementLp Complex.I (by norm_num) M m n =
      h1LatticeElementLp M m n := by
  unfold generalizedH1LatticeElementLp h1LatticeElementLp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t =>
    congrFun (generalizedH1LatticeElement_I M m n) t

/-- At `τ=i`, the generalized arbitrary-lattice predicate is exactly the
original first-Hermite predicate. -/
theorem isGeneralizedGaborFrameForLattice_I_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice Complex.I (by norm_num) M ↔
      IsGaborFrameForLattice M := by
  simp only [IsGeneralizedGaborFrameForLattice, IsGaborFrameForLattice,
    generalizedH1LatticeElementLp_I]

/-- The inverse quarter rotation. -/
noncomputable def inverseFourierRotationMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

@[simp] lemma fourierRotationMatrix_mul_inverse :
    fourierRotationMatrix * inverseFourierRotationMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierRotationMatrix, inverseFourierRotationMatrix, rotationMatrix,
      Matrix.mul_apply]

lemma fourierTau_involutive {τ : ℂ} (hτ : 0 < τ.im) :
    fourierTau (fourierTau τ) = τ := by
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  unfold fourierTau
  field_simp [hτ0]

/-- Covariance for the inverse Fourier generator, obtained from forward
Fourier covariance and involutivity. -/
theorem isGeneralizedGaborFrameForLattice_inverseFourier_iff
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGeneralizedGaborFrameForLattice (fourierTau τ) (fourierTau_im_pos hτ)
        (inverseFourierRotationMatrix * M) ↔
      IsGeneralizedGaborFrameForLattice τ hτ M := by
  have h := (isGeneralizedGaborFrameForLattice_fourier_iff
    (fourierTau τ) (fourierTau_im_pos hτ)
    (inverseFourierRotationMatrix * M)).symm
  have hmatrix :
      fourierRotationMatrix * (inverseFourierRotationMatrix * M) = M := by
    rw [← Matrix.mul_assoc, fourierRotationMatrix_mul_inverse, one_mul]
  rw [hmatrix] at h
  simpa only [fourierTau_involutive hτ] using h

/-- Bruhat decomposition on the open cell whose upper-right entry is
nonzero.  Positivity is not needed for the algebraic identity, but will be
needed when the middle diagonal matrix is implemented by an `L²` dilation. -/
theorem bruhat_decomposition
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1)
    (hb : S 0 1 ≠ 0) :
    S = lowerShearMatrix (S 1 1 / S 0 1) *
      symplecticDilationMatrix (S 0 1) * fourierRotationMatrix *
      lowerShearMatrix (S 0 0 / S 0 1) := by
  have hδ : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, symplecticDilationMatrix,
      fourierRotationMatrix, rotationMatrix, Matrix.mul_apply]
  all_goals try field_simp [hb] <;> ring_nf at hδ ⊢ <;> linarith

/-- The lower-triangular determinant-one cell. -/
theorem triangular_decomposition
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1)
    (hb : S 0 1 = 0) (ha : S 0 0 ≠ 0) :
    S = lowerShearMatrix (S 1 0 / S 0 0) *
      symplecticDilationMatrix (S 0 0) := by
  have hδ : S 0 0 * S 1 1 = 1 := by
    simpa [Matrix.det_fin_two, hb] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, symplecticDilationMatrix, Matrix.mul_apply]
  all_goals try assumption
  all_goals try field_simp [ha] <;> ring_nf at hδ ⊢ <;> linarith

/-- Transport through the positive Bruhat cell, using successively a lower
shear, Fourier transform, positive dilation, and a second lower shear. -/
theorem exists_generator_reduction_bruhat_pos
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1)
    (hb : 0 < S 0 1) (τ : ℂ) (hτ : 0 < τ.im)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (τ' : ℂ) (hτ' : 0 < τ'.im),
      IsGeneralizedGaborFrameForLattice τ' hτ' (S * M) ↔
        IsGeneralizedGaborFrameForLattice τ hτ M := by
  let ηr : ℝ := S 0 0 / S 0 1
  let τ₁ : ℂ := τ + ηr
  have hτ₁ : 0 < τ₁.im := by
    dsimp [τ₁, ηr]
    simpa using hτ
  have h₁ :
      IsGeneralizedGaborFrameForLattice τ₁ hτ₁
          (lowerShearMatrix ηr * M) ↔
        IsGeneralizedGaborFrameForLattice τ hτ M := by
    simpa [τ₁] using
      (isGeneralizedGaborFrameForLattice_lowerShear_iff ηr τ hτ M)
  let τ₂ : ℂ := fourierTau τ₁
  have hτ₂ : 0 < τ₂.im := fourierTau_im_pos hτ₁
  have h₂ :
      IsGeneralizedGaborFrameForLattice τ₂ hτ₂
          (fourierRotationMatrix * (lowerShearMatrix ηr * M)) ↔
        IsGeneralizedGaborFrameForLattice τ₁ hτ₁
          (lowerShearMatrix ηr * M) := by
    simpa [τ₂] using
      (isGeneralizedGaborFrameForLattice_fourier_iff τ₁ hτ₁
        (lowerShearMatrix ηr * M))
  let τ₃ : ℂ := dilatedTau (S 0 1) τ₂
  have hτ₃ : 0 < τ₃.im := dilatedTau_im_pos hb hτ₂
  have h₃ :
      IsGeneralizedGaborFrameForLattice τ₃ hτ₃
          (symplecticDilationMatrix (S 0 1) *
            (fourierRotationMatrix * (lowerShearMatrix ηr * M))) ↔
        IsGeneralizedGaborFrameForLattice τ₂ hτ₂
          (fourierRotationMatrix * (lowerShearMatrix ηr * M)) := by
    simpa [τ₃] using
      (isGeneralizedGaborFrameForLattice_dilation_iff (S 0 1) hb τ₂ hτ₂
        (fourierRotationMatrix * (lowerShearMatrix ηr * M)))
  let ηl : ℝ := S 1 1 / S 0 1
  let τ₄ : ℂ := τ₃ + ηl
  have hτ₄ : 0 < τ₄.im := by
    dsimp [τ₄, ηl]
    simpa using hτ₃
  have h₄ :
      IsGeneralizedGaborFrameForLattice τ₄ hτ₄
          (lowerShearMatrix ηl *
            (symplecticDilationMatrix (S 0 1) *
              (fourierRotationMatrix * (lowerShearMatrix ηr * M)))) ↔
        IsGeneralizedGaborFrameForLattice τ₃ hτ₃
          (symplecticDilationMatrix (S 0 1) *
            (fourierRotationMatrix * (lowerShearMatrix ηr * M))) := by
    simpa [τ₄] using
      (isGeneralizedGaborFrameForLattice_lowerShear_iff ηl τ₃ hτ₃
        (symplecticDilationMatrix (S 0 1) *
          (fourierRotationMatrix * (lowerShearMatrix ηr * M))))
  have hmatrix :
      lowerShearMatrix ηl *
          (symplecticDilationMatrix (S 0 1) *
            (fourierRotationMatrix * (lowerShearMatrix ηr * M))) = S * M := by
    have hdecomp : S = lowerShearMatrix ηl *
        symplecticDilationMatrix (S 0 1) * fourierRotationMatrix *
        lowerShearMatrix ηr := by
      simpa only [ηl, ηr] using bruhat_decomposition hdet (ne_of_gt hb)
    calc
      _ = (lowerShearMatrix ηl *
            symplecticDilationMatrix (S 0 1) * fourierRotationMatrix *
            lowerShearMatrix ηr) * M := by simp only [Matrix.mul_assoc]
      _ = S * M := congrArg (fun A => A * M) hdecomp.symm
  refine ⟨τ₄, hτ₄, ?_⟩
  rw [← hmatrix]
  exact h₄.trans (h₃.trans (h₂.trans h₁))

/-- Transport through the positive lower-triangular cell. -/
theorem exists_generator_reduction_triangular_pos
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1)
    (hb : S 0 1 = 0) (ha : 0 < S 0 0)
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (τ' : ℂ) (hτ' : 0 < τ'.im),
      IsGeneralizedGaborFrameForLattice τ' hτ' (S * M) ↔
        IsGeneralizedGaborFrameForLattice τ hτ M := by
  let τ₁ : ℂ := dilatedTau (S 0 0) τ
  have hτ₁ : 0 < τ₁.im := dilatedTau_im_pos ha hτ
  have h₁ :
      IsGeneralizedGaborFrameForLattice τ₁ hτ₁
          (symplecticDilationMatrix (S 0 0) * M) ↔
        IsGeneralizedGaborFrameForLattice τ hτ M := by
    simpa [τ₁] using
      (isGeneralizedGaborFrameForLattice_dilation_iff (S 0 0) ha τ hτ M)
  let η : ℝ := S 1 0 / S 0 0
  let τ₂ : ℂ := τ₁ + η
  have hτ₂ : 0 < τ₂.im := by
    dsimp [τ₂, η]
    simpa using hτ₁
  have h₂ :
      IsGeneralizedGaborFrameForLattice τ₂ hτ₂
          (lowerShearMatrix η * (symplecticDilationMatrix (S 0 0) * M)) ↔
        IsGeneralizedGaborFrameForLattice τ₁ hτ₁
          (symplecticDilationMatrix (S 0 0) * M) := by
    simpa [τ₂] using
      (isGeneralizedGaborFrameForLattice_lowerShear_iff η τ₁ hτ₁
        (symplecticDilationMatrix (S 0 0) * M))
  have hmatrix :
      lowerShearMatrix η * (symplecticDilationMatrix (S 0 0) * M) = S * M := by
    have hdecomp : S = lowerShearMatrix η *
        symplecticDilationMatrix (S 0 0) := by
      simpa only [η] using triangular_decomposition hdet hb (ne_of_gt ha)
    calc
      _ = (lowerShearMatrix η * symplecticDilationMatrix (S 0 0)) * M := by
        simp only [Matrix.mul_assoc]
      _ = S * M := congrArg (fun A => A * M) hdecomp.symm
  refine ⟨τ₂, hτ₂, ?_⟩
  rw [← hmatrix]
  exact h₂.trans h₁

@[simp] lemma det_neg_matrix_two (S : Matrix (Fin 2) (Fin 2) ℝ) :
    (-S).det = S.det := by
  simp [Matrix.det_fin_two]

/-- Every determinant-one change of phase-space coordinates carries the
first generalized Hermite window to another member of the same family and
preserves the frame predicate.  This is exactly the metaplectic reduction
needed to pass from a separable lattice to an arbitrary lattice. -/
theorem exists_generator_reduction
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1)
    (τ : ℂ) (hτ : 0 < τ.im) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (τ' : ℂ) (hτ' : 0 < τ'.im),
      IsGeneralizedGaborFrameForLattice τ' hτ' (S * M) ↔
        IsGeneralizedGaborFrameForLattice τ hτ M := by
  by_cases hbzero : S 0 1 = 0
  · have ha : S 0 0 ≠ 0 := by
      intro ha0
      rw [Matrix.det_fin_two, ha0, hbzero] at hdet
      norm_num at hdet
    by_cases hapos : 0 < S 0 0
    · exact exists_generator_reduction_triangular_pos hdet hbzero hapos τ hτ M
    · have haneg : S 0 0 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hapos) ha
      have hnegdet : (-S).det = 1 := by simpa using hdet
      have hnegzero : (-S) 0 1 = 0 := by simp [hbzero]
      have hnegpos : 0 < (-S) 0 0 := by simpa using (neg_pos.mpr haneg)
      rcases exists_generator_reduction_triangular_pos
          hnegdet hnegzero hnegpos τ hτ M with ⟨τ', hτ', htransport⟩
      refine ⟨τ', hτ', ?_⟩
      have htransport' :
          IsGeneralizedGaborFrameForLattice τ' hτ' (-(S * M)) ↔
            IsGeneralizedGaborFrameForLattice τ hτ M := by
        simpa only [neg_mul] using htransport
      exact (isGeneralizedGaborFrameForLattice_neg_iff τ' hτ' (S * M)).symm.trans
        htransport'
  · by_cases hbpos : 0 < S 0 1
    · exact exists_generator_reduction_bruhat_pos hdet hbpos τ hτ M
    · have hbneg : S 0 1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hbpos) hbzero
      have hnegdet : (-S).det = 1 := by simpa using hdet
      have hnegpos : 0 < (-S) 0 1 := by simpa using (neg_pos.mpr hbneg)
      rcases exists_generator_reduction_bruhat_pos
          hnegdet hnegpos τ hτ M with ⟨τ', hτ', htransport⟩
      refine ⟨τ', hτ', ?_⟩
      have htransport' :
          IsGeneralizedGaborFrameForLattice τ' hτ' (-(S * M)) ↔
            IsGeneralizedGaborFrameForLattice τ hτ M := by
        simpa only [neg_mul] using htransport
      exact (isGeneralizedGaborFrameForLattice_neg_iff τ' hτ' (S * M)).symm.trans
        htransport'

end LyubarskiiNes.GeneralLattice
