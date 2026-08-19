import LeanCode.RationalDensity.RankScaling
import LeanCode.ZakTransform.Criterion
import LeanCode.TorsionJets.FourierResidue
import Mathlib.Analysis.Calculus.SmoothSeries

open MeasureTheory
open scoped Matrix ComplexOrder BigOperators ENNReal

namespace LyubarskiiNes.RationalDensity

lemma int_mem_symmetric_Icc_of_natAbs_le {k : ℤ} {M : ℕ} (h : k.natAbs ≤ M) :
    k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
  rw [Finset.mem_Icc]
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk]
    constructor <;> omega
  · rw [hk]
    constructor <;> omega

lemma finset_int_subset_symmetric_Icc (s : Finset ℤ) :
    ∃ M : ℕ, s ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
  refine ⟨s.sup Int.natAbs, ?_⟩
  intro k hk
  exact int_mem_symmetric_Icc_of_natAbs_le
    (Finset.le_sup (s := s) (f := Int.natAbs) hk)

/-- The residue `b ∈ {0, ..., q-1}` used in the student's reindexing
`m = q * ell - b`. -/
def intNegResidueFin {q : ℕ} (hq : 0 < q) (m : ℤ) : Fin q :=
  ⟨Int.toNat ((-m) % (q : ℤ)), by
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have hlt : (-m) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hq)).2 hlt⟩

/-- Integer value of the residue representative `intNegResidueFin`. -/
lemma intNegResidueFin_val_int {q : ℕ} (hq : 0 < q) (m : ℤ) :
    (((intNegResidueFin hq m : Fin q) : ℕ) : ℤ) =
      (-m) % (q : ℤ) := by
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hnonneg : 0 ≤ (-m) % (q : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hqZ)
  simp [intNegResidueFin, Int.toNat_of_nonneg hnonneg]

/-- Concrete form of the student's integer decomposition
`m = q * ell - b`, with `b` chosen as the representative of `-m` modulo `q`. -/
lemma int_m_eq_q_mul_sub_negResidue {q : ℕ} (hq : 0 < q) (m : ℤ) :
    (q : ℤ) * ((m + (((intNegResidueFin hq m : Fin q) : ℕ) : ℤ)) / (q : ℤ)) -
        (((intNegResidueFin hq m : Fin q) : ℕ) : ℤ) = m := by
  have hbval := intNegResidueFin_val_int hq m
  have hdiv : (q : ℤ) ∣
      m + (((intNegResidueFin hq m : Fin q) : ℕ) : ℤ) := by
    rw [hbval]
    refine ⟨-((-m) / (q : ℤ)), ?_⟩
    have h := Int.mul_ediv_add_emod (-m) (q : ℤ)
    calc
      m + (-m) % (q : ℤ) = -((q : ℤ) * ((-m) / (q : ℤ))) := by omega
      _ = (q : ℤ) * -((-m) / (q : ℤ)) := by ring
  have hmul := Int.mul_ediv_cancel' hdiv
  omega

/-- Existence form of the student's reindexing `m = q * ell - b`. -/
lemma int_m_eq_q_mul_sub_exists {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∃ ell : ℤ, ∃ b : Fin q,
      m = (q : ℤ) * ell - (((b : Fin q) : ℕ) : ℤ) := by
  refine ⟨(m + (((intNegResidueFin hq m : Fin q) : ℕ) : ℤ)) / (q : ℤ),
    intNegResidueFin hq m, ?_⟩
  exact (int_m_eq_q_mul_sub_negResidue hq m).symm

lemma zmod_fin_nat_int_cast_eq_finEquiv {p : ℕ} [NeZero p] (r : Fin p) :
    (((r : ℕ) : ℤ) : ZMod p) = ZMod.finEquiv p r := by
  cases p with
  | zero => exact Fin.elim0 r
  | succ p =>
      have hval : ZMod.val (ZMod.finEquiv (p + 1) r) = r.val := by
        rfl
      rw [← hval, Int.cast_natCast]
      exact ZMod.natCast_zmod_val (ZMod.finEquiv (p + 1) r)

/-- Uniqueness of the student's reindexing `m = q * ell - b` with
`b : Fin q`. -/
lemma int_q_mul_sub_fin_unique {q : ℕ} (hq : 0 < q)
    {ell₁ ell₂ : ℤ} {b₁ b₂ : Fin q}
    (h : (q : ℤ) * ell₁ - (((b₁ : Fin q) : ℕ) : ℤ) =
      (q : ℤ) * ell₂ - (((b₂ : Fin q) : ℕ) : ℤ)) :
    ell₁ = ell₂ ∧ b₁ = b₂ := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hbcast :
      ((((b₁ : Fin q) : ℕ) : ℤ) : ZMod q) =
        ((((b₂ : Fin q) : ℕ) : ℤ) : ZMod q) := by
    have hcast := congrArg (fun n : ℤ => (n : ZMod q)) h
    simpa using hcast
  have hb : b₁ = b₂ := by
    rw [zmod_fin_nat_int_cast_eq_finEquiv, zmod_fin_nat_int_cast_eq_finEquiv] at hbcast
    exact (ZMod.finEquiv q).injective hbcast
  subst b₂
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hell : (q : ℤ) * ell₁ = (q : ℤ) * ell₂ := by omega
  exact ⟨mul_left_cancel₀ hqZ hell, rfl⟩

/-- Injectivity of the student's map `(ell, b) ↦ q * ell - b`. -/
lemma int_q_mul_sub_fin_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective
      (fun eb : ℤ × Fin q =>
        (q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ)) := by
  intro eb₁ eb₂ h
  rcases eb₁ with ⟨ell₁, b₁⟩
  rcases eb₂ with ⟨ell₂, b₂⟩
  rcases int_q_mul_sub_fin_unique hq (ell₁ := ell₁) (ell₂ := ell₂)
      (b₁ := b₁) (b₂ := b₂) h with ⟨hell, hb⟩
  simp [hell, hb]

/-- Surjectivity of the student's map `(ell, b) ↦ q * ell - b`. -/
lemma int_q_mul_sub_fin_surjective {q : ℕ} (hq : 0 < q) :
    Function.Surjective
      (fun eb : ℤ × Fin q =>
        (q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ)) := by
  intro m
  rcases int_m_eq_q_mul_sub_exists hq m with ⟨ell, b, hm⟩
  exact ⟨(ell, b), hm.symm⟩

/-- Equivalence form of the student's reindexing
`m ↔ (ell, b)` with `m = q * ell - b`. -/
noncomputable def intQMulSubFinEquiv (q : ℕ) (hq : 0 < q) : ℤ × Fin q ≃ ℤ :=
  Equiv.ofBijective
    (fun eb : ℤ × Fin q =>
      (q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ))
    ⟨int_q_mul_sub_fin_injective hq, int_q_mul_sub_fin_surjective hq⟩

/-- `tsum` reindexing through the student's equivalence
`(ell, b) ↦ q * ell - b`. -/
theorem tsum_int_qMulSubFinEquiv
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {q : ℕ} (hq : 0 < q) (f : ℤ → E) :
    (∑' m : ℤ, f m) =
      ∑' eb : ℤ × Fin q,
        f ((q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ)) := by
  symm
  simpa [intQMulSubFinEquiv] using
    (Equiv.tsum_eq (intQMulSubFinEquiv q hq) f)

/-- Nested-sum form of the student's reindexing `m = q * ell - b`, with
the finite residue index outside.  This is the shape used in the first
Parseval step of the dense coefficient calculation. -/
theorem tsum_int_qMulSubFinEquiv_fin_tsum
    {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] [T0Space E]
    {q : ℕ} (hq : 0 < q) (f : ℤ → E)
    (hf : Summable fun be : Fin q × ℤ =>
      f ((q : ℤ) * be.2 - (((be.1 : Fin q) : ℕ) : ℤ))) :
    (∑' m : ℤ, f m) =
      ∑ b : Fin q, ∑' ell : ℤ,
        f ((q : ℤ) * ell - (((b : Fin q) : ℕ) : ℤ)) := by
  have hEq :
      (∑' m : ℤ, f m) =
        ∑' be : Fin q × ℤ,
          f ((q : ℤ) * be.2 - (((be.1 : Fin q) : ℕ) : ℤ)) := by
    have hbase := tsum_int_qMulSubFinEquiv (q := q) hq f
    have hswap :
        (∑' be : Fin q × ℤ,
          f ((q : ℤ) * be.2 - (((be.1 : Fin q) : ℕ) : ℤ))) =
          ∑' eb : ℤ × Fin q,
            f ((q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ)) := by
      simpa using
        (Equiv.tsum_eq (Equiv.prodComm (Fin q) ℤ)
          (fun eb : ℤ × Fin q =>
            f ((q : ℤ) * eb.1 - (((eb.2 : Fin q) : ℕ) : ℤ))))
    rw [hbase, ← hswap]
  calc
    (∑' m : ℤ, f m) =
        ∑' be : Fin q × ℤ,
          f ((q : ℤ) * be.2 - (((be.1 : Fin q) : ℕ) : ℤ)) := hEq
    _ = ∑' b : Fin q, ∑' ell : ℤ,
          f ((q : ℤ) * ell - (((b : Fin q) : ℕ) : ℤ)) := by
          simpa using
            (Summable.tsum_prod
              (f := fun be : Fin q × ℤ =>
                f ((q : ℤ) * be.2 - (((be.1 : Fin q) : ℕ) : ℤ))) hf)
    _ = ∑ b : Fin q, ∑' ell : ℤ,
          f ((q : ℤ) * ell - (((b : Fin q) : ℕ) : ℤ)) := by
          rw [tsum_fintype]

/-- Product-indexed coefficient energy appearing in the frozen frame predicate. -/
noncomputable def productCoeffEnergy (α β : ℝ)
    (x : Lp ℂ 2 (volume : Measure ℝ)) : ℝ :=
  ∑' mn : ℤ × ℤ,
    ‖inner ℂ x (LyubarskiiNes.h1_element_Lp α β mn.1 mn.2)‖ ^ 2

/-- The paper's rational-Zak scale `γ = α q`. -/
noncomputable def rationalZakGamma (α : ℝ) (q : ℕ) : ℝ :=
  α * (q : ℝ)

/-- The fiberization scale `η = γ / p`, equal to `1 / β` under the rational
density hypothesis. -/
noncomputable def rationalZakEta (α : ℝ) (p q : ℕ) : ℝ :=
  rationalZakGamma α q / (p : ℝ)

/-- The paper-side `p × q` rational Zak matrix for the first Hermite window,
with rows indexed by the fiber component and columns by the translation
residue. -/
noncomputable def rationalZakPMatrixH1 (α : ℝ) (p q : ℕ) :
    ℝ × ℝ → Matrix (Fin p) (Fin q) ℂ :=
  fun z s t =>
    Zak.zakTransform (rationalZakGamma α q) gaussianH1C
      (z.1 + α * ((t : ℕ) : ℝ) +
        rationalZakGamma α q * ((s : ℕ) : ℝ) / (p : ℝ)) z.2

/-- The residual-shape rational Zak matrix `M : ℂ^p → ℂ^q`, namely the adjoint
of the paper-side matrix.  The coefficient-energy identity has the form
`‖P_gᴴ v‖²`, hence this orientation matches the downstream `M *ᵥ v`. -/
noncomputable def rationalZakMatrix (α : ℝ) (p q : ℕ) :
    ℝ × ℝ → Matrix (Fin q) (Fin p) ℂ :=
  fun z => (rationalZakPMatrixH1 α p q z)ᴴ

/-- The unnormalized finite Fourier row-change identified by the corrected
rational-Zak coefficient identity.  With `η = γ / p`, its entries are
`D(ξ)_{a,r} = exp(-2π i (η r ξ + a r / p))`. -/
noncomputable def rationalPositiveFourierRowChange (α : ℝ) (p q : ℕ) :
    ℝ × ℝ → Matrix (Fin p) (Fin p) ℂ :=
  fun z a r =>
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I *
      (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (z.2 : ℂ) +
        ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)))

/-- The fixed primitive root used by the finite Fourier part of the corrected
row-change matrix. -/
noncomputable def rationalPositiveFourierRoot (p : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I / (p : ℂ))

/-- The frequency-dependent diagonal phase in the corrected row-change
factorization `D(ξ) = F · diag(phase(ξ))`. -/
noncomputable def rationalPositiveFourierPhase (α : ℝ) (p q : ℕ)
    (z : ℝ × ℝ) : Fin p → ℂ :=
  fun r =>
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I *
      (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (z.2 : ℂ)))

/-- Corrected adjoint-oriented matrix for the shifted honest fiber `v_x`.
Mathematically this is `(D(ξ) P(s,ξ))^* = P(s,ξ)^* D(ξ)^*`, where `D` is the
unnormalized finite Fourier row-change. -/
noncomputable def rationalPositiveCorrectedZakMatrix (α : ℝ) (p q : ℕ) :
    ℝ × ℝ → Matrix (Fin q) (Fin p) ℂ :=
  fun z => rationalZakMatrix α p q z *
    (rationalPositiveFourierRowChange α p q z)ᴴ

/-- Coefficient normalization for the unnormalized corrected matrix.  The
student calculation gives `η γ / p^2`; since `γ = pη`, this is `η^2 / p`, but
the unsimplified form keeps the Zak scales visible. -/
noncomputable def rationalPositiveCorrectedCoeffScale (α : ℝ) (p q : ℕ) : ℝ :=
  rationalZakEta α p q * rationalZakGamma α q / ((p : ℝ) ^ 2)

/-- Every entry of the unnormalized finite Fourier row-change has modulus one. -/
lemma rationalPositiveFourierRowChange_entry_norm
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (a r : Fin p) :
    ‖rationalPositiveFourierRowChange α p q z a r‖ = 1 := by
  unfold rationalPositiveFourierRowChange
  let θ : ℝ :=
    ((r : ℕ) : ℝ) * rationalZakEta α p q * z.2 +
      ((a : ℕ) : ℝ) * ((r : ℕ) : ℝ) / (p : ℝ)
  have harg :
      -(2 * (Real.pi : ℂ)) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (z.2 : ℂ) +
            ((a : ℕ) : ℂ) * ((r : ℕ) : ℂ) / (p : ℂ)) =
        ((-(2 * Real.pi) * θ : ℝ) : ℂ) * Complex.I := by
    dsimp [θ]
    norm_num [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div]
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The adjoint of the unnormalized finite Fourier row-change is uniformly
bounded in Lean's finite sup norm.  The sharp Euclidean statement is
`D(ξ)^*D(ξ)=pI`; this cruder sup-norm estimate is enough for integrability and
upper-bound bookkeeping. -/
lemma rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_le
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ≤
      (p : ℝ) * ‖w‖ := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hC : 0 ≤ (p : ℝ) * ‖w‖ := mul_nonneg hp_nonneg (norm_nonneg _)
  refine Zak.pi_norm_le_of_forall_norm_le
    ((rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w) hC ?_
  intro i
  calc
    ‖((rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w) i‖
        = ‖∑ j : Fin p, ((rationalPositiveFourierRowChange α p q z)ᴴ i j) * w j‖ := by
            simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j : Fin p, ‖((rationalPositiveFourierRowChange α p q z)ᴴ i j) * w j‖ :=
          norm_sum_le _ _
    _ = ∑ j : Fin p, ‖w j‖ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [norm_mul]
          simp [Matrix.conjTranspose_apply,
            rationalPositiveFourierRowChange_entry_norm]
    _ ≤ ∑ _j : Fin p, ‖w‖ := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact Zak.pi_norm_apply_le_norm w j
    _ = (p : ℝ) * ‖w‖ := by
          simp

/-- Squared-norm version of
`rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_le`. -/
lemma rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_sq_le
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ^ 2 ≤
      (p : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  have hle := rationalPositiveFourierRowChange_conjTranspose_mulVec_norm_le
    α p q z w
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc
    ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ^ 2
        ≤ ((p : ℝ) * ‖w‖) ^ 2 := hpow
    _ = (p : ℝ) ^ 2 * ‖w‖ ^ 2 := by ring

/-- A square finite matrix with injective `mulVec` has a positive homogeneous
lower bound for Lean's finite sup norm. -/
lemma finiteSquare_exists_mulVec_norm_sq_lower_bound_of_injective
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (hn : 0 < Fintype.card n)
    (hsphere : (Metric.sphere (0 : n → ℂ) 1).Nonempty)
    (hinj : Function.Injective A.mulVec) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℂ,
      c * ‖x‖ ^ 2 ≤ ‖A *ᵥ x‖ ^ 2 := by
  have hG : (Aᴴ * A).PosDef := Zak.gram_posDef_of_mulVec_injective A hinj
  rcases Zak.gram_posDef_exists_pos_lower_bound_on_unit_sphere A hG hsphere with
    ⟨c, hc, hunit⟩
  let c0 : ℝ := c / (Fintype.card n : ℝ)
  have hn_real : 0 < (Fintype.card n : ℝ) := by exact_mod_cast hn
  refine ⟨c0, div_pos hc hn_real, ?_⟩
  have hunit_norm : ∀ x : n → ℂ, x ∈ Metric.sphere (0 : n → ℂ) 1 →
      c0 ≤ ‖A *ᵥ x‖ ^ 2 := by
    intro x hx
    have hquad := hunit x hx
    have hle_card := Zak.re_dotProduct_star_self_le_card_mul_norm_sq (A *ᵥ x)
    have hquad_eq : RCLike.re (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)) =
        (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)).re := by
      rw [Zak.gram_quadratic_eq_dotProduct_mulVec]
      rfl
    have hc_le_card : c ≤ (Fintype.card n : ℝ) * ‖A *ᵥ x‖ ^ 2 := by
      exact le_trans (by simpa [hquad_eq] using hquad) hle_card
    exact (div_le_iff₀ hn_real).2 (by simpa [mul_comm, c0] using hc_le_card)
  simpa using (Zak.mulVec_norm_sq_lower_bound_of_unit_sphere A hunit_norm)

/-- The Fourier root used in the row-change matrix is primitive when
`p > 0`. -/
lemma rationalPositiveFourierRoot_isPrimitiveRoot {p : ℕ} (hp : 0 < p) :
    IsPrimitiveRoot (rationalPositiveFourierRoot p) p := by
  have hp_ne : p ≠ 0 := Nat.ne_of_gt hp
  have hroot := Complex.isPrimitiveRoot_exp p hp_ne
  have hzeta :
      rationalPositiveFourierRoot p =
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)))⁻¹ := by
    unfold rationalPositiveFourierRoot
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hzeta]
  exact hroot.inv

/-- The fixed DFT core of the corrected row-change has a positive homogeneous
lower bound independent of the frequency point. -/
lemma rationalPositiveFourierCore_conjTranspose_exists_lower_bound {p : ℕ}
    (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin p → ℂ,
      c * ‖w‖ ^ 2 ≤
        ‖(LyubarskiiNes.ThetaFunctions.dft_matrix p
            (rationalPositiveFourierRoot p))ᴴ *ᵥ w‖ ^ 2 := by
  have hroot : IsPrimitiveRoot (rationalPositiveFourierRoot p) p :=
    rationalPositiveFourierRoot_isPrimitiveRoot hp
  let F := LyubarskiiNes.ThetaFunctions.dft_matrix p (rationalPositiveFourierRoot p)
  have hdetF : F.det ≠ 0 := by
    simpa [F] using
      LyubarskiiNes.ThetaFunctions.dft_matrix_det_ne_zero_of_isPrimitiveRoot hroot
  have hdetFH : (Fᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hdetF
  have hunit_det : IsUnit (Fᴴ).det := IsUnit.mk0 _ hdetFH
  have hunit : IsUnit Fᴴ := ((Fᴴ).isUnit_iff_isUnit_det).mpr hunit_det
  have hinj : Function.Injective (Fᴴ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hsphere : (Metric.sphere (0 : Fin p → ℂ) 1).Nonempty := by
    classical
    let i : Fin p := ⟨0, hp⟩
    let e : Fin p → ℂ := Pi.single i (1 : ℂ)
    refine ⟨e, ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    rw [Pi.norm_def]
    rw [← NNReal.coe_one]
    rw [NNReal.coe_inj]
    apply le_antisymm
    · apply Finset.sup_le
      intro j _hj
      by_cases hji : j = i
      · subst j
        simp [e]
      · simp [e, Pi.single_eq_of_ne hji]
    · have hi : ‖e i‖₊ = 1 := by
        simp [e]
      calc
        1 = ‖e i‖₊ := hi.symm
        _ ≤ Finset.univ.sup (fun b => ‖e b‖₊) :=
          Finset.le_sup (s := Finset.univ) (f := fun b => ‖e b‖₊) (Finset.mem_univ i)
  simpa [F] using
    finiteSquare_exists_mulVec_norm_sq_lower_bound_of_injective (Fᴴ)
      (by simpa using hp) hsphere hinj

/-- The corrected row-change factors as a fixed DFT matrix followed by a
frequency-dependent diagonal phase. -/
lemma rationalPositiveFourierRowChange_eq_dft_mul_diagonal
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) :
    rationalPositiveFourierRowChange α p q z =
      LyubarskiiNes.ThetaFunctions.dft_matrix p (rationalPositiveFourierRoot p) *
        Matrix.diagonal (rationalPositiveFourierPhase α p q z) := by
  ext a r
  simp [rationalPositiveFourierRowChange, LyubarskiiNes.ThetaFunctions.dft_matrix,
    rationalPositiveFourierRoot, rationalPositiveFourierPhase,
    Matrix.mul_apply, Matrix.diagonal_apply]
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_add]
  congr 1
  norm_num [Nat.cast_mul]
  ring_nf

/-- Continuity of the finite Fourier row-change matrix as a function of the
frequency point. -/
lemma continuous_rationalPositiveFourierRowChange (α : ℝ) (p q : ℕ) :
    Continuous (rationalPositiveFourierRowChange α p q) := by
  apply continuous_matrix
  intro a r
  dsimp [rationalPositiveFourierRowChange]
  fun_prop

/-- Every diagonal phase in the row-change factorization has modulus one. -/
lemma rationalPositiveFourierPhase_norm
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (r : Fin p) :
    ‖rationalPositiveFourierPhase α p q z r‖ = 1 := by
  unfold rationalPositiveFourierPhase
  let θ : ℝ := ((r : ℕ) : ℝ) * rationalZakEta α p q * z.2
  have harg :
      -(2 * (Real.pi : ℂ)) * Complex.I *
          (((r : ℕ) : ℂ) * (rationalZakEta α p q : ℂ) * (z.2 : ℂ)) =
        ((-(2 * Real.pi) * θ : ℝ) : ℂ) * Complex.I := by
    dsimp [θ]
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Coordinate formula for applying the conjugate-transposed diagonal phase. -/
lemma rationalPositiveFourierPhase_diagonal_conjTranspose_mulVec_apply
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (w : Fin p → ℂ) (i : Fin p) :
    (((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w) i) =
      star (rationalPositiveFourierPhase α p q z i) * w i := by
  classical
  change (∑ x : Fin p,
      ((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ i x) * w x) =
    star (rationalPositiveFourierPhase α p q z i) * w i
  calc
    (∑ x : Fin p,
        ((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ i x) * w x) =
        ((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ i i) * w i := by
      refine Finset.sum_eq_single
        (s := (Finset.univ : Finset (Fin p)))
        (f := fun x : Fin p =>
          ((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ i x) * w x)
        (a := i) ?_ ?_
      · intro b _hb hbi
        simp [Matrix.conjTranspose_apply, hbi]
      · intro hi
        simp at hi
    _ = star (rationalPositiveFourierPhase α p q z i) * w i := by
      simp [Matrix.conjTranspose_apply]

/-- The conjugate-transposed diagonal phase preserves Lean's finite sup norm. -/
lemma rationalPositiveFourierPhase_diagonal_conjTranspose_mulVec_norm
    (α : ℝ) (p q : ℕ) (z : ℝ × ℝ) (w : Fin p → ℂ) :
    ‖(Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w‖ =
      ‖w‖ := by
  classical
  have hcoord_norm : ∀ i,
      ‖(((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w) i)‖ =
        ‖w i‖ := by
    intro i
    rw [rationalPositiveFourierPhase_diagonal_conjTranspose_mulVec_apply,
      norm_mul, norm_star, rationalPositiveFourierPhase_norm]
    simp
  apply le_antisymm
  · refine Zak.pi_norm_le_of_forall_norm_le _ (norm_nonneg _) ?_
    intro i
    calc
      ‖(((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w) i)‖ =
          ‖w i‖ := hcoord_norm i
      _ ≤ ‖w‖ := Zak.pi_norm_apply_le_norm w i
  · refine Zak.pi_norm_le_of_forall_norm_le w (norm_nonneg _) ?_
    intro i
    calc
      ‖w i‖ =
          ‖(((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w) i)‖ :=
        (hcoord_norm i).symm
      _ ≤ ‖(Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w‖ :=
          Zak.pi_norm_apply_le_norm
            ((Matrix.diagonal (rationalPositiveFourierPhase α p q z))ᴴ *ᵥ w) i

/-- Uniform lower bound for the adjoint of the student-corrected row-change.
The constant is the fixed DFT lower bound; the frequency-dependent diagonal
phase is norm-preserving. -/
lemma rationalPositiveFourierRowChange_conjTranspose_exists_lower_bound
    (α : ℝ) {p : ℕ} (q : ℕ) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℝ × ℝ) (w : Fin p → ℂ),
      c * ‖w‖ ^ 2 ≤
        ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ^ 2 := by
  rcases rationalPositiveFourierCore_conjTranspose_exists_lower_bound hp with
    ⟨c, hc, hF⟩
  refine ⟨c, hc, ?_⟩
  intro z w
  let F := LyubarskiiNes.ThetaFunctions.dft_matrix p (rationalPositiveFourierRoot p)
  let E := Matrix.diagonal (rationalPositiveFourierPhase α p q z)
  have hfact : rationalPositiveFourierRowChange α p q z = F * E := by
    simpa [F, E] using rationalPositiveFourierRowChange_eq_dft_mul_diagonal α p q z
  have hrewrite :
      (rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w =
        Eᴴ *ᵥ (Fᴴ *ᵥ w) := by
    calc
      (rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w =
          ((F * E)ᴴ) *ᵥ w := by
            rw [hfact]
      _ = (Eᴴ * Fᴴ) *ᵥ w := by
            rw [Matrix.conjTranspose_mul]
      _ = Eᴴ *ᵥ (Fᴴ *ᵥ w) := by
            simp [Matrix.mulVec_mulVec]
  have hnorm : ‖Eᴴ *ᵥ (Fᴴ *ᵥ w)‖ = ‖Fᴴ *ᵥ w‖ := by
    simpa [E] using
      rationalPositiveFourierPhase_diagonal_conjTranspose_mulVec_norm
        α p q z (Fᴴ *ᵥ w)
  calc
    c * ‖w‖ ^ 2 ≤ ‖Fᴴ *ᵥ w‖ ^ 2 := by
      simpa [F] using hF w
    _ = ‖Eᴴ *ᵥ (Fᴴ *ᵥ w)‖ ^ 2 := by
      rw [hnorm]
    _ = ‖(rationalPositiveFourierRowChange α p q z)ᴴ *ᵥ w‖ ^ 2 := by
      rw [hrewrite]
end LyubarskiiNes.RationalDensity
