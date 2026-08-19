import LeanCode.GeneralLattice.FrameTransfer

open MeasureTheory
open scoped Matrix BigOperators

namespace LyubarskiiNes.GeneralLattice

/-- Reverse the second basis vector.  This changes the sign of the determinant
but presents the same lattice because `n ↦ -n` permutes `ℤ`. -/
noncomputable def reverseSecondBasis
    (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![M 0 0, -M 0 1; M 1 0, -M 1 1]

@[simp] lemma det_reverseSecondBasis (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (reverseSecondBasis M).det = -M.det := by
  simp [reverseSecondBasis, Matrix.det_fin_two]
  ring

@[simp] lemma latticeTime_reverseSecondBasis
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeTime (reverseSecondBasis M) m n = latticeTime M m (-n) := by
  simp [latticeTime, reverseSecondBasis]

@[simp] lemma latticeFrequency_reverseSecondBasis
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeFrequency (reverseSecondBasis M) m n = latticeFrequency M m (-n) := by
  simp [latticeFrequency, reverseSecondBasis]

lemma h1LatticeElement_reverseSecondBasis
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    h1LatticeElement (reverseSecondBasis M) m n = h1LatticeElement M m (-n) := by
  funext t
  simp [h1LatticeElement]

lemma h1LatticeElementLp_reverseSecondBasis
    (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    h1LatticeElementLp (reverseSecondBasis M) m n = h1LatticeElementLp M m (-n) := by
  unfold h1LatticeElementLp
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun t =>
    congrFun (h1LatticeElement_reverseSecondBasis M m n) t

/-- A negatively oriented basis can be replaced by a positively oriented one
without changing the Gabor family (up to the bijection `n ↦ -n`). -/
theorem isGaborFrameForLattice_reverseSecondBasis_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGaborFrameForLattice (reverseSecondBasis M) ↔ IsGaborFrameForLattice M := by
  rw [isGaborFrameForLattice_iff_isFrameFamily,
    isGaborFrameForLattice_iff_isFrameFamily]
  have hfamily : h1LatticeElementLp (reverseSecondBasis M) =
      fun m n => h1LatticeElementLp M m (-n) := by
    funext m n
    exact h1LatticeElementLp_reverseSecondBasis M m n
  rw [hfamily]
  simpa using
    (isFrameFamily_reindex (h1LatticeElementLp M) (Equiv.refl ℤ) (Equiv.neg ℤ))

/-- The chosen positively oriented presentation of a matrix lattice. -/
noncomputable def positiveOrientation
    (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if 0 < M.det then M else reverseSecondBasis M

theorem det_positiveOrientation_pos
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) :
    0 < (positiveOrientation M).det := by
  unfold positiveOrientation
  split_ifs with h
  · exact h
  · rw [det_reverseSecondBasis]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hM)

@[simp] theorem abs_det_positiveOrientation
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    |(positiveOrientation M).det| = |M.det| := by
  unfold positiveOrientation
  split_ifs
  · rfl
  · rw [det_reverseSecondBasis, abs_neg]

theorem isGaborFrameForLattice_positiveOrientation_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGaborFrameForLattice (positiveOrientation M) ↔ IsGaborFrameForLattice M := by
  unfold positiveOrientation
  split_ifs
  · rfl
  · exact isGaborFrameForLattice_reverseSecondBasis_iff M

/-- The canonical basis matrix with the same positive covolume as `A`. -/
noncomputable def canonicalCovolumeMatrix (δ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![δ, 0; 0, 1]

@[simp] lemma det_canonicalCovolumeMatrix (δ : ℝ) :
    (canonicalCovolumeMatrix δ).det = δ := by
  simp [canonicalCovolumeMatrix, Matrix.det_fin_two]

/-- The determinant-one matrix which sends `A` to
`diag(det A, 1)`. -/
noncomputable def canonicalNormalizer
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  canonicalCovolumeMatrix A.det * A⁻¹

lemma canonicalNormalizer_mul
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    canonicalNormalizer A * A = canonicalCovolumeMatrix A.det := by
  have hunit : IsUnit A.det := IsUnit.mk0 _ hA
  simp [canonicalNormalizer, Matrix.mul_assoc, Matrix.nonsing_inv_mul A hunit]

@[simp] lemma det_canonicalNormalizer
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    (canonicalNormalizer A).det = 1 := by
  rw [canonicalNormalizer, Matrix.det_mul, det_canonicalCovolumeMatrix,
    Matrix.det_nonsing_inv]
  simp [hA]

/-- Squared dilation parameter in the explicit Iwasawa decomposition. -/
noncomputable def iwasawaNuSq (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (S 0 0) ^ 2 + (S 0 1) ^ 2

/-- Positive dilation parameter in the explicit Iwasawa decomposition. -/
noncomputable def iwasawaNu (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt (iwasawaNuSq S)

/-- Lower-shear parameter in the explicit Iwasawa decomposition. -/
noncomputable def iwasawaEta (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (S 0 0 * S 1 0 + S 0 1 * S 1 1) / iwasawaNuSq S

noncomputable def iwasawaSigmaRe (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  S 0 0 / iwasawaNu S

noncomputable def iwasawaSigmaIm (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  S 0 1 / iwasawaNu S

noncomputable def lowerShearMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; η, 1]

noncomputable def symplecticDilationMatrix (ν : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ν, 0; 0, ν⁻¹]

noncomputable def rotationMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u, v; -v, u]

@[simp] lemma latticeTime_lowerShearMatrix_mul
    (η : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeTime (lowerShearMatrix η * M) m n = latticeTime M m n := by
  simp [latticeTime, lowerShearMatrix, Matrix.mul_apply]

@[simp] lemma latticeFrequency_lowerShearMatrix_mul
    (η : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeFrequency (lowerShearMatrix η * M) m n =
      η * latticeTime M m n + latticeFrequency M m n := by
  simp [latticeFrequency, latticeTime, lowerShearMatrix, Matrix.mul_apply]
  ring

@[simp] lemma latticeTime_symplecticDilationMatrix_mul
    (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeTime (symplecticDilationMatrix ν * M) m n = ν * latticeTime M m n := by
  simp [latticeTime, symplecticDilationMatrix, Matrix.mul_apply]
  ring

@[simp] lemma latticeFrequency_symplecticDilationMatrix_mul
    (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (m n : ℤ) :
    latticeFrequency (symplecticDilationMatrix ν * M) m n =
      ν⁻¹ * latticeFrequency M m n := by
  simp [latticeFrequency, symplecticDilationMatrix, Matrix.mul_apply]
  ring

lemma iwasawaNuSq_pos
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    0 < iwasawaNuSq S := by
  have hne : S 0 0 ≠ 0 ∨ S 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Matrix.det_fin_two, h.1, h.2] at hdet
    norm_num at hdet
  unfold iwasawaNuSq
  rcases hne with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

lemma iwasawaNu_pos
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    0 < iwasawaNu S := by
  exact Real.sqrt_pos.2 (iwasawaNuSq_pos hdet)

lemma iwasawaNu_sq
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    (iwasawaNu S) ^ 2 = iwasawaNuSq S := by
  unfold iwasawaNu
  exact Real.sq_sqrt (le_of_lt (iwasawaNuSq_pos hdet))

/-- The rotation parameters in Iwasawa decomposition lie on the unit circle. -/
lemma iwasawaSigma_unit
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    (iwasawaSigmaRe S) ^ 2 + (iwasawaSigmaIm S) ^ 2 = 1 := by
  rw [iwasawaSigmaRe, iwasawaSigmaIm, div_pow, div_pow,
    ← add_div, iwasawaNu_sq hdet]
  exact div_self (ne_of_gt (iwasawaNuSq_pos hdet))

/-- Explicit two-dimensional Iwasawa decomposition
`S = V_η D_ν R_σ` for determinant-one matrices. -/
theorem iwasawa_decomposition
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    S = lowerShearMatrix (iwasawaEta S) *
      symplecticDilationMatrix (iwasawaNu S) *
      rotationMatrix (iwasawaSigmaRe S) (iwasawaSigmaIm S) := by
  have hνpos : 0 < iwasawaNu S := iwasawaNu_pos hdet
  have hν : iwasawaNu S ≠ 0 := ne_of_gt hνpos
  have hνsq : (iwasawaNu S) ^ 2 = iwasawaNuSq S := iwasawaNu_sq hdet
  have hr : iwasawaNuSq S ≠ 0 := ne_of_gt (iwasawaNuSq_pos hdet)
  have hδ : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hbottom0 :
      S 1 0 = iwasawaEta S * S 0 0 - S 0 1 / (iwasawaNu S) ^ 2 := by
    rw [iwasawaEta, hνsq]
    field_simp [hr]
    simp [iwasawaNuSq]
    linear_combination -(S 0 1) * hδ
  have hbottom1 :
      S 1 1 = iwasawaEta S * S 0 1 + S 0 0 / (iwasawaNu S) ^ 2 := by
    rw [iwasawaEta, hνsq]
    field_simp [hr]
    simp [iwasawaNuSq]
    linear_combination (S 0 0) * hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, symplecticDilationMatrix, rotationMatrix,
      iwasawaSigmaRe, iwasawaSigmaIm, Matrix.mul_apply]
  · field_simp
  · field_simp
  · field_simp [hν] at hbottom0 ⊢
    exact hbottom0
  · field_simp [hν] at hbottom1 ⊢
    exact hbottom1

/-- Upper-half-plane parameter of the generalized Hermite window produced by
the shear and dilation parts of Iwasawa decomposition. -/
noncomputable def iwasawaTau (S : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (iwasawaEta S : ℂ) + Complex.I / ((iwasawaNu S : ℂ) ^ 2)

lemma iwasawaTau_im_pos
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hdet : S.det = 1) :
    0 < (iwasawaTau S).im := by
  have hνpos : 0 < iwasawaNu S := iwasawaNu_pos hdet
  have hν : iwasawaNu S ≠ 0 := ne_of_gt hνpos
  unfold iwasawaTau
  rw [Complex.add_im]
  norm_num [Complex.div_im, hν]
  rw [show ((iwasawaNu S : ℂ) ^ 2).re = (iwasawaNu S) ^ 2 by
    simp [pow_two, Complex.mul_re]]
  positivity

end LyubarskiiNes.GeneralLattice
