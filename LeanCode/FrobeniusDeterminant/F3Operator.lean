import LeanCode.FrobeniusDeterminant.F1Factorization
import LeanCode.FrobeniusDeterminant.PrimitiveDerivative

/-!
# WF_F3op_1 — STEP 1 of the F3 node: the cyclic minor as a row-operator determinant

This file develops the self-contained linear-algebra / calculus core of the F3 node
(`minor_as_polynomial_operator`).  The genuine analytic content of Steps 2–3 (the
confluent Leibniz collapse to a polynomial in `𝔡` applied to `Ξ_p`, and the argument
reindexing) sits downstream; here we close the operator-through-determinant identity.

The row operator is `A f z = paperDerivScale · deriv f z + lam · f z`.  Its action on a
determinant whose columns are single-variable theta functions is computed by
differentiating the Leibniz expansion row by row: because row `r` of the minor depends on
only the coordinate `x_r`, the operator `A` distributes through the Leibniz sum, and the
result is again a determinant with `A` applied entrywise.
-/

open Complex Matrix
open scoped ContDiff

namespace LyubarskiiNes.FrobeniusDeterminant

open LyubarskiiNes.FrobeniusDeterminant.FrobeniusFactor LyubarskiiNes.FrobeniusDeterminant.ThetaDimension
  LyubarskiiNes.TorsionJets

/-! ## The single-variable row operator `A f = 𝔡 f + λ f`. -/

/-- The paper's first-order row operator `A f = (2πi)⁻¹·f' + λ·f`.  This is the entrywise
operator that produces the primitive-derivative matrix from the pure theta matrix. -/
noncomputable def rowOp (lam : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => paperDerivScale * deriv f z + lam * f z

/-- The single-variable theta column function `φ_s(z) = θ_τ(z + s/p)`. -/
noncomputable def thetaCol (p : ℕ) (τ : ℂ) (s : Fin p) : ℂ → ℂ :=
  fun z => jacobiTheta₂ (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ

/-- The `z`-derivative of the shifted theta column, as a `HasDerivAt` statement.  It is
`jacobiTheta₂(·,τ)` precomposed with a translation, so its derivative is `jacobiTheta₂'`
at the shifted point. -/
theorem hasDerivAt_thetaCol {p : ℕ} {τ : ℂ} (hτ : 0 < τ.im) (s : Fin p) (z : ℂ) :
    HasDerivAt (thetaCol p τ s)
      (jacobiTheta₂' (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ) z := by
  have harg : HasDerivAt (fun w : ℂ => w + ((s : ℕ) : ℂ) / (p : ℂ)) 1 z := by
    simpa using (hasDerivAt_id z).add_const (((s : ℕ) : ℂ) / (p : ℂ))
  have hth : HasDerivAt (fun w : ℂ => jacobiTheta₂ w τ)
      (jacobiTheta₂' (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ) (z + ((s : ℕ) : ℂ) / (p : ℂ)) :=
    hasDerivAt_jacobiTheta₂_fst (z + ((s : ℕ) : ℂ) / (p : ℂ)) hτ
  have : HasDerivAt ((fun w : ℂ => jacobiTheta₂ w τ) ∘ fun w : ℂ => w + ((s : ℕ) : ℂ) / (p : ℂ))
      (jacobiTheta₂' (z + ((s : ℕ) : ℂ) / (p : ℂ)) τ) z := by
    simpa using hth.comp z harg
  exact this

theorem thetaCol_differentiable {p : ℕ} {τ : ℂ} (hτ : 0 < τ.im) (s : Fin p) :
    Differentiable ℂ (thetaCol p τ s) :=
  fun z => (hasDerivAt_thetaCol hτ s z).differentiableAt

/-- The row operator applied to `φ_s` matches the entry of the primitive-derivative
matrix at the corresponding sample point.  This is the entry-level rewrite that turns
the minor into a determinant of `A (φ_s)`-values. -/
theorem rowOp_thetaCol_eq_entry {p q : ℕ} [NeZero q]
    (τ lam a : ℂ) (hτ : 0 < τ.im) (t : Fin q) (s : Fin p) :
    rowOp lam (thetaCol p τ s) (a + ((t : ℕ) : ℂ) / (q : ℂ)) =
      primitiveThetaDerivativeMatrix p q τ lam a t s := by
  unfold rowOp primitiveThetaDerivativeMatrix
  -- Column term: `scaledDeriv (thetaShift ..) = paperDerivScale · jacobiTheta₂' (..)`.
  rw [scaledDeriv_thetaShift p τ hτ s (a + ((t : ℕ) : ℂ) / (q : ℂ)),
    LyubarskiiNes.ThetaFunctions.thetaShift_apply]
  -- `deriv (thetaCol ..) = jacobiTheta₂' (..)` and `thetaCol .. = jacobiTheta₂ (..)`.
  have hderiv : deriv (thetaCol p τ s) (a + ((t : ℕ) : ℂ) / (q : ℂ)) =
      jacobiTheta₂' (a + ((t : ℕ) : ℂ) / (q : ℂ) + ((s : ℕ) : ℂ) / (p : ℂ)) τ :=
    (hasDerivAt_thetaCol hτ s (a + ((t : ℕ) : ℂ) / (q : ℂ))).deriv
  rw [hderiv]
  rfl

/-! ## The coordinate-wise row operator and the distribution lemma (STEP 1 core)

For a multivariable function `G : (Fin p → ℂ) → ℂ`, `coordOp lam r₀ G` applies the
first-order operator `A = 𝔡 + λ` in the single coordinate `r₀`.  The distribution lemma
says that when `G` is a product `∏ r, h r (y r)` of single-variable functions, applying
`coordOp` in coordinate `r₀` factors the operator onto the `r₀`-th factor, and iterating
over all coordinates turns `∏ r, h r (y r)` into `∏ r, (A (h r)) (y r)`.  This is the
Leibniz distribution that drives the operator-through-determinant identity. -/

/-- The first-order row operator `A = 𝔡 + λ` applied in the single coordinate `r₀`. -/
noncomputable def coordOp {p : ℕ} (lam : ℂ) (r₀ : Fin p) (G : (Fin p → ℂ) → ℂ) :
    (Fin p → ℂ) → ℂ :=
  fun y => paperDerivScale * deriv (fun t : ℂ => G (Function.update y r₀ t)) (y r₀) +
    lam * G y

/-- Restricting a product `∏ r, h r (y r)` to the `r₀`-coordinate slice through `y`
gives the single-variable function `t ↦ (∏ r ≠ r₀, h r (y r)) · h r₀ t`. -/
theorem prod_update_slice {p : ℕ} (h : Fin p → ℂ → ℂ) (y : Fin p → ℂ) (r₀ : Fin p) :
    (fun t : ℂ => ∏ r, h r (Function.update y r₀ t r)) =
      fun t : ℂ => (∏ r ∈ Finset.univ.erase r₀, h r (y r)) * h r₀ t := by
  funext t
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r₀)]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro r hr
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]
  · rw [Function.update_self]

/-- **Single-coordinate distribution.**  Applying the coordinate-`r₀` operator to a
product of single-variable functions factors it onto the `r₀`-th factor: replaces
`h r₀ (y r₀)` by `(A (h r₀)) (y r₀)`, leaving the others untouched. -/
theorem coordOp_prod {p : ℕ} (lam : ℂ) (r₀ : Fin p) (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r)) (y : Fin p → ℂ) :
    coordOp lam r₀ (fun z : Fin p → ℂ => ∏ r, h r (z r)) y =
      (∏ r ∈ Finset.univ.erase r₀, h r (y r)) * rowOp lam (h r₀) (y r₀) := by
  unfold coordOp rowOp
  rw [prod_update_slice h y r₀]
  -- deriv of `t ↦ K · h r₀ t` at `y r₀` is `K · deriv (h r₀) (y r₀)`.
  have hderiv : deriv (fun t : ℂ => (∏ r ∈ Finset.univ.erase r₀, h r (y r)) * h r₀ t) (y r₀) =
      (∏ r ∈ Finset.univ.erase r₀, h r (y r)) * deriv (h r₀) (y r₀) :=
    deriv_const_mul _ (hdiff r₀ (y r₀))
  rw [hderiv]
  -- also the `lam * G y` term: `G y = K · h r₀ (y r₀)`.
  have hGy : (fun z : Fin p → ℂ => ∏ r, h r (z r)) y =
      (∏ r ∈ Finset.univ.erase r₀, h r (y r)) * h r₀ (y r₀) := by
    simp only
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r₀)]
  rw [hGy]
  ring

/-- **Product form is preserved.**  `coordOp lam r₀` applied to the product function
`∏ r, h r (·_r)` is again a product function `∏ r, (Function.update h r₀ (A (h r₀))) r (·_r)`,
i.e. only the `r₀`-th factor changes, to `A (h r₀)`.  This is the closure property that
lets the coordinate operators be folded over all coordinates. -/
theorem coordOp_prod_eq_prod_update {p : ℕ} (lam : ℂ) (r₀ : Fin p) (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r)) :
    coordOp lam r₀ (fun z : Fin p → ℂ => ∏ r, h r (z r)) =
      fun z : Fin p → ℂ => ∏ r, (Function.update h r₀ (rowOp lam (h r₀))) r (z r) := by
  funext y
  rw [coordOp_prod lam r₀ h hdiff y]
  -- RHS product: split off `r₀`, its factor is `rowOp lam (h r₀) (y r₀)`, others unchanged.
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r₀), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro r hr
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]

/-- The full multivariable operator: fold the coordinate operators over a list of
coordinates.  Folding over `List.finRange p` applies `A = 𝔡 + λ` in every coordinate. -/
noncomputable def foldCoordOp {p : ℕ} (lam : ℂ) (l : List (Fin p))
    (G : (Fin p → ℂ) → ℂ) : (Fin p → ℂ) → ℂ :=
  l.foldr (fun r₀ acc => coordOp lam r₀ acc) G

/-- Folding the coordinate operators over a *nodup* list of coordinates applied to a
product function `∏ r, h r (·_r)` produces the product with each factor over the list
replaced by its `rowOp`.  Proved by induction on the list, using the closure property
`coordOp_prod_eq_prod_update` and preservation of differentiability. -/
theorem foldCoordOp_prod {p : ℕ} (lam : ℂ) (l : List (Fin p)) (hnd : l.Nodup)
    (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r))
    (hC2 : ∀ r, Differentiable ℂ (deriv (h r))) :
    foldCoordOp lam l (fun z : Fin p → ℂ => ∏ r, h r (z r)) =
      fun z : Fin p → ℂ => ∏ r, (if r ∈ l then rowOp lam (h r) else h r) (z r) := by
  induction l generalizing h with
  | nil =>
      funext z; simp [foldCoordOp]
  | cons a t ih =>
      have hant : a ∉ t := (List.nodup_cons.mp hnd).1
      have htnd : t.Nodup := (List.nodup_cons.mp hnd).2
      -- Inductive step: apply the tail-fold to the product, then coordOp at `a`.
      have hgoal : foldCoordOp lam (a :: t) (fun z : Fin p → ℂ => ∏ r, h r (z r)) =
          coordOp lam a (fun z : Fin p → ℂ =>
            ∏ r, (if r ∈ t then rowOp lam (h r) else h r) (z r)) := by
        simp only [foldCoordOp, List.foldr_cons]
        rw [show t.foldr (fun r₀ acc => coordOp lam r₀ acc)
              (fun z : Fin p → ℂ => ∏ r, h r (z r))
            = fun z : Fin p → ℂ => ∏ r, (if r ∈ t then rowOp lam (h r) else h r) (z r) from
          ih htnd h hdiff hC2]
      rw [hgoal]
      -- The tail-updated family `h' r = if r ∈ t then rowOp (h r) else h r` is differentiable.
      set h' : Fin p → ℂ → ℂ := fun r => if r ∈ t then rowOp lam (h r) else h r with hh'
      have hdiff' : ∀ r, Differentiable ℂ (h' r) := by
        intro r
        by_cases hr : r ∈ t
        · simp only [hh', if_pos hr]
          unfold rowOp
          exact (Differentiable.const_mul (hC2 r) _).add (Differentiable.const_mul (hdiff r) _)
        · simp only [hh', if_neg hr]; exact hdiff r
      rw [coordOp_prod_eq_prod_update lam a h' hdiff']
      funext z
      refine Finset.prod_congr rfl ?_
      intro r _
      by_cases hra : r = a
      · subst hra
        rw [Function.update_self]
        simp only [hh', List.mem_cons, true_or, if_true, if_neg hant]
      · rw [Function.update_of_ne hra]
        simp only [hh', List.mem_cons]
        by_cases hrt : r ∈ t
        · simp [hrt, hra]
        · simp [hrt, hra]

/-! ### Linearity of the coordinate operator and the fold (needed to push through Leibniz)

To move the operator fold inside the Leibniz sum we need `coordOp` — and hence the whole
fold — to be additive and `smul`-compatible.  `coordOp` involves a coordinate derivative,
so additivity holds only for functions whose coordinate slices are differentiable.  We
therefore track "coordinate-slice differentiability" (`SliceDiff`) and show it is preserved
by `coordOp` and closed under the operations used. -/

/-- Coordinate-slice differentiability: for every coordinate `r₀` and every base point `y`,
the single-variable slice `t ↦ G (update y r₀ t)` is differentiable at `y r₀`.  This is the
hypothesis that makes `coordOp` additive. -/
def SliceDiff {p : ℕ} (G : (Fin p → ℂ) → ℂ) : Prop :=
  ∀ (r₀ : Fin p) (y : Fin p → ℂ),
    DifferentiableAt ℂ (fun t : ℂ => G (Function.update y r₀ t)) (y r₀)

/-- A product of single-variable functions has differentiable coordinate slices. -/
theorem sliceDiff_prod {p : ℕ} (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r)) :
    SliceDiff (fun z : Fin p → ℂ => ∏ r, h r (z r)) := by
  intro r₀ y
  have := prod_update_slice h y r₀
  rw [this]
  exact (differentiableAt_const _).mul (hdiff r₀ (y r₀))

/-- `coordOp` is additive on coordinate-slice-differentiable functions. -/
theorem coordOp_add {p : ℕ} (lam : ℂ) (r₀ : Fin p) (G H : (Fin p → ℂ) → ℂ)
    (hG : SliceDiff G) (hH : SliceDiff H) :
    coordOp lam r₀ (fun y => G y + H y) =
      fun y => coordOp lam r₀ G y + coordOp lam r₀ H y := by
  funext y
  unfold coordOp
  have hslice : (fun t : ℂ => G (Function.update y r₀ t) + H (Function.update y r₀ t)) =
      (fun t : ℂ => G (Function.update y r₀ t)) + (fun t : ℂ => H (Function.update y r₀ t)) :=
    rfl
  rw [show (fun t : ℂ => (fun y => G y + H y) (Function.update y r₀ t)) =
      (fun t : ℂ => G (Function.update y r₀ t)) + (fun t : ℂ => H (Function.update y r₀ t)) from rfl,
    deriv_add (hG r₀ y) (hH r₀ y)]
  simp only [Pi.add_apply]
  ring

/-- `coordOp` is `smul`-compatible (pulls a constant scalar out). -/
theorem coordOp_smul {p : ℕ} (lam : ℂ) (r₀ : Fin p) (c : ℂ) (G : (Fin p → ℂ) → ℂ) :
    coordOp lam r₀ (fun y => c • G y) = fun y => c • coordOp lam r₀ G y := by
  funext y
  unfold coordOp
  rw [show (fun t : ℂ => (fun y => c • G y) (Function.update y r₀ t)) =
      (fun t : ℂ => c • G (Function.update y r₀ t)) from rfl]
  simp only [smul_eq_mul]
  rw [deriv_const_mul_field]
  ring

/-- `coordOp` preserves coordinate-slice differentiability, provided the coordinate
derivatives themselves have differentiable slices.  For products of `C^∞` single-variable
functions (our theta case) this always holds; we state it with an explicit `C²`-type
hypothesis packaged as slice differentiability of `G` and of all its coordinate
derivatives.  Rather than develop the general theory, downstream we apply the fold only to
Leibniz product terms and use `sliceDiff_prod` after `foldCoordOp_prod`; hence the fold's
additivity is invoked on already-product-form data. -/
theorem foldCoordOp_smul {p : ℕ} (lam : ℂ) (l : List (Fin p)) (c : ℂ)
    (G : (Fin p → ℂ) → ℂ) :
    foldCoordOp lam l (fun y => c • G y) = fun y => c • foldCoordOp lam l G y := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [foldCoordOp, List.foldr_cons] at ih ⊢
      rw [ih, coordOp_smul]

/-- Folding the coordinate operators over a list applied to a single product summand of
the given shape is again a product (hence coordinate-slice differentiable) at each stage.
Packaged for the additivity induction below. -/
theorem sliceDiff_foldCoordOp_prod {p : ℕ} (lam : ℂ) (l : List (Fin p)) (hnd : l.Nodup)
    (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r))
    (hC2 : ∀ r, Differentiable ℂ (deriv (h r))) :
    SliceDiff (foldCoordOp lam l (fun z : Fin p → ℂ => ∏ r, h r (z r))) := by
  rw [foldCoordOp_prod lam l hnd h hdiff hC2]
  apply sliceDiff_prod
  intro r
  by_cases hr : r ∈ l
  · simp only [if_pos hr]
    unfold rowOp
    exact (Differentiable.const_mul (hC2 r) _).add (Differentiable.const_mul (hdiff r) _)
  · simp only [if_neg hr]; exact hdiff r

/-- `SliceDiff` is closed under pointwise addition. -/
theorem SliceDiff.add {p : ℕ} {G H : (Fin p → ℂ) → ℂ} (hG : SliceDiff G) (hH : SliceDiff H) :
    SliceDiff (fun y => G y + H y) := by
  intro r₀ y
  exact (hG r₀ y).add (hH r₀ y)

/-- **Additivity of the fold** on coordinate-slice-differentiable functions.  Proved by
induction on the coordinate list, using `coordOp_add` and the fact that the fold preserves
`SliceDiff` under the hypothesis that every stage of both folds stays `SliceDiff`.  Here we
supply that hypothesis directly as `hGl`/`hHl`: for every *suffix* fold, `G` and `H` remain
`SliceDiff`.  For our product/sum-of-product data these hold by `sliceDiff_foldCoordOp_prod`
and `SliceDiff.add`. -/
theorem foldCoordOp_add {p : ℕ} (lam : ℂ) (l : List (Fin p))
    (G H : (Fin p → ℂ) → ℂ)
    (hGl : ∀ t : List (Fin p), t <:+ l → SliceDiff (foldCoordOp lam t G))
    (hHl : ∀ t : List (Fin p), t <:+ l → SliceDiff (foldCoordOp lam t H)) :
    foldCoordOp lam l (fun y => G y + H y) =
      fun y => foldCoordOp lam l G y + foldCoordOp lam l H y := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have htsuf : t <:+ (a :: t) := List.suffix_cons a t
      have ihres := ih (fun t' ht' => hGl t' (ht'.trans htsuf))
        (fun t' ht' => hHl t' (ht'.trans htsuf))
      simp only [foldCoordOp, List.foldr_cons] at ihres ⊢
      rw [ihres]
      exact coordOp_add lam a _ _
        (hGl t htsuf) (hHl t htsuf)

/-- `coordOp` applied to the zero function is the zero function. -/
theorem coordOp_zero {p : ℕ} (lam : ℂ) (r₀ : Fin p) :
    coordOp lam r₀ (fun _ : Fin p → ℂ => (0 : ℂ)) = fun _ => 0 := by
  funext y
  unfold coordOp
  simp

/-- The fold of the zero function is the zero function. -/
theorem foldCoordOp_zero {p : ℕ} (lam : ℂ) (l : List (Fin p)) :
    foldCoordOp lam l (fun _ : Fin p → ℂ => (0 : ℂ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [foldCoordOp, List.foldr_cons] at ih ⊢
      rw [ih, coordOp_zero]

/-- **Update commutes with a coordinate shift.**  Updating the shifted point
`(fun i => y i + w i)` at `r₀` with value `t + w r₀` equals shifting the updated point
`Function.update y r₀ t`. -/
theorem update_add_shift {p : ℕ} (y w : Fin p → ℂ) (r₀ : Fin p) (t : ℂ) :
    Function.update (fun i => y i + w i) r₀ (t + w r₀)
      = fun i => (Function.update y r₀ t) i + w i := by
  funext i
  by_cases hi : i = r₀
  · subst hi; simp [Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- **`coordOp` is translation-covariant.**  Precomposing with the coordinate shift
`y ↦ (fun i => y i + w i)` commutes with `coordOp lam r₀`:
`coordOp lam r₀ (fun y => f (y + w)) = fun y => (coordOp lam r₀ f) (y + w)`.
The chain rule (`deriv_comp_add_const`, shift by `w r₀`) handles the derivative term. -/
theorem coordOp_comp_add_const {p : ℕ} (lam : ℂ) (r₀ : Fin p) (f : (Fin p → ℂ) → ℂ)
    (w : Fin p → ℂ) :
    coordOp lam r₀ (fun y : Fin p → ℂ => f (fun i => y i + w i))
      = fun y : Fin p → ℂ => (coordOp lam r₀ f) (fun i => y i + w i) := by
  funext y
  unfold coordOp
  -- Derivative term: rewrite the slice as `t ↦ g (t + w r₀)` with
  -- `g s = f (update (y+w) r₀ s)`, then apply `deriv_comp_add_const`.
  have hslice : (fun t : ℂ => (fun y : Fin p → ℂ => f (fun i => y i + w i))
        (Function.update y r₀ t))
      = (fun t : ℂ =>
          (fun s : ℂ => f (Function.update (fun i => y i + w i) r₀ s)) (t + w r₀)) := by
    funext t
    simp only []
    rw [update_add_shift y w r₀ t]
  rw [hslice,
    deriv_comp_add_const (f := fun s : ℂ => f (Function.update (fun i => y i + w i) r₀ s))
      (a := w r₀) (x := y r₀)]

/-- A scalar multiple of a product function is `SliceDiff` (its fold too), and folds
commute with the scalar.  Recorded as `SliceDiff` closure under `smul`. -/
theorem SliceDiff.smul {p : ℕ} (c : ℂ) {G : (Fin p → ℂ) → ℂ} (hG : SliceDiff G) :
    SliceDiff (fun y => c • G y) := by
  intro r₀ y
  have : DifferentiableAt ℂ (fun t : ℂ => c * G (Function.update y r₀ t)) (y r₀) :=
    (hG r₀ y).const_mul c
  simpa only [smul_eq_mul] using this

/-- The fold of a finite scalar-weighted sum of product functions is `SliceDiff`, and the
fold distributes over the sum (pulling each scalar through).  Both are proved together by
induction on the index finset so that the `SliceDiff` needed for additivity of the next
step is available. -/
theorem foldCoordOp_finset_sum {p : ℕ} (lam : ℂ) (l : List (Fin p)) (hnd : l.Nodup)
    {ι : Type*} (I : Finset ι) (c : ι → ℂ) (hfam : ι → Fin p → ℂ → ℂ)
    (hdiff : ∀ i r, Differentiable ℂ (hfam i r))
    (hC2 : ∀ i r, Differentiable ℂ (deriv (hfam i r))) :
    (foldCoordOp lam l (fun y : Fin p → ℂ => ∑ i ∈ I, c i • ∏ r, hfam i r (y r)) =
      fun y : Fin p → ℂ =>
        ∑ i ∈ I, c i • foldCoordOp lam l (fun z => ∏ r, hfam i r (z r)) y) ∧
    (∀ t : List (Fin p), t <:+ l →
      SliceDiff (foldCoordOp lam t
        (fun y : Fin p → ℂ => ∑ i ∈ I, c i • ∏ r, hfam i r (y r)))) := by
  classical
  induction I using Finset.induction with
  | empty =>
      constructor
      · funext y; simp only [Finset.sum_empty]
        rw [foldCoordOp_zero]
      · intro t _
        simp only [Finset.sum_empty]
        rw [foldCoordOp_zero]
        intro r₀ y; simpa using differentiableAt_const (0 : ℂ)
  | insert a s ha ih =>
      obtain ⟨iheq, ihSD⟩ := ih
      -- `SliceDiff` of the (folded) head summand over any suffix.
      have hSDhead : ∀ t : List (Fin p), t <:+ l →
          SliceDiff (foldCoordOp lam t (fun z : Fin p → ℂ => c a • ∏ r, hfam a r (z r))) := by
        intro t htsuf
        rw [foldCoordOp_smul]
        exact SliceDiff.smul _
          (sliceDiff_foldCoordOp_prod lam t (hnd.sublist htsuf.sublist)
            (hfam a) (hdiff a) (hC2 a))
      have hsplit : (fun y : Fin p → ℂ => ∑ i ∈ insert a s, c i • ∏ r, hfam i r (y r)) =
          (fun y : Fin p → ℂ =>
            (c a • ∏ r, hfam a r (y r)) + ∑ i ∈ s, c i • ∏ r, hfam i r (y r)) := by
        funext z; rw [Finset.sum_insert ha]
      -- distribution
      have heq : foldCoordOp lam l
            (fun y : Fin p → ℂ => ∑ i ∈ insert a s, c i • ∏ r, hfam i r (y r)) =
          fun y : Fin p → ℂ => ∑ i ∈ insert a s,
            c i • foldCoordOp lam l (fun z => ∏ r, hfam i r (z r)) y := by
        funext y
        rw [hsplit, foldCoordOp_add lam l _ _ (hSDhead) (ihSD)]
        simp only []
        rw [congrFun iheq y, Finset.sum_insert ha, foldCoordOp_smul]
      refine ⟨heq, ?_⟩
      intro t htsuf
      rw [hsplit, foldCoordOp_add lam t _ _
        (fun t' ht' => hSDhead t' (ht'.trans htsuf))
        (fun t' ht' => ihSD t' (ht'.trans htsuf))]
      exact SliceDiff.add (hSDhead t htsuf) (ihSD t htsuf)

/-- **Operator through the determinant (STEP 1 master identity).**  Applying the full
coordinate operator fold `∏_r A_{y_r}` to the Frobenius-type determinant
`G(y) = det[h s (y r)]` and evaluating at `x` equals the determinant with `A = 𝔡 + λ`
applied to each column function `h s`.  This is the operator-through-determinant identity:
the multivariable operator distributes over the Leibniz expansion, and on each permutation
term collapses (`foldCoordOp_prod`) to a product of `rowOp`-applied single-variable
factors, reassembling the `rowOp` determinant. -/
theorem foldCoordOp_det {p : ℕ} (lam : ℂ) (h : Fin p → ℂ → ℂ)
    (hdiff : ∀ r, Differentiable ℂ (h r))
    (hC2 : ∀ r, Differentiable ℂ (deriv (h r))) (x : Fin p → ℂ) :
    foldCoordOp lam (List.finRange p)
      (fun y : Fin p → ℂ => (Matrix.of fun r s : Fin p => h s (y r)).det) x =
      (Matrix.of fun r s : Fin p => rowOp lam (h s) (x r)).det := by
  classical
  -- Column families indexed by permutations: `hfam σ r = h (σ⁻¹ r)`.
  set hfam : Equiv.Perm (Fin p) → Fin p → ℂ → ℂ := fun σ r => h (σ⁻¹ r) with hhfam
  -- Leibniz expansion of `G(y)` as a scalar-weighted sum of product functions.
  have hGexp : (fun y : Fin p → ℂ => (Matrix.of fun r s : Fin p => h s (y r)).det) =
      (fun y : Fin p → ℂ =>
        ∑ σ : Equiv.Perm (Fin p), (Equiv.Perm.sign σ : ℂ) • ∏ r, hfam σ r (y r)) := by
    funext y
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [smul_eq_mul]
    congr 1
    -- Goal: `∏ i, of[..] (σ i) i = ∏ r, hfam σ r (y r)`.  Reindex RHS by `σ`.
    rw [← Equiv.prod_comp σ (fun r => hfam σ r (y r))]
    refine Finset.prod_congr rfl ?_
    intro i _
    simp [hhfam, Matrix.of_apply]
  rw [hGexp]
  -- Push the fold through the scalar-weighted sum.
  have hkey := (foldCoordOp_finset_sum lam (List.finRange p) (List.nodup_finRange p)
    (Finset.univ : Finset (Equiv.Perm (Fin p))) (fun σ => (Equiv.Perm.sign σ : ℂ)) hfam
    (fun σ r => by simpa [hhfam] using hdiff (σ⁻¹ r))
    (fun σ r => by simpa [hhfam] using hC2 (σ⁻¹ r))).1
  rw [congrFun hkey x]
  -- Each permutation term: the fold of a product collapses to a product of `rowOp` factors.
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [smul_eq_mul]
  have hprod := congrFun (foldCoordOp_prod lam (List.finRange p) (List.nodup_finRange p)
    (hfam σ) (fun r => by simpa [hhfam] using hdiff (σ⁻¹ r))
    (fun r => by simpa [hhfam] using hC2 (σ⁻¹ r))) x
  simp only [List.mem_finRange, if_true] at hprod
  rw [hprod]
  -- `(sgn σ) * ∏ r, rowOp lam (h (σ⁻¹ r)) (x r) = (sgn σ) * ∏ i, rowOp lam (h i) (x (σ i))`.
  congr 1
  rw [← Equiv.prod_comp σ (fun r => rowOp lam (hfam σ r) (x r))]
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [hhfam, Matrix.of_apply]

/-- **The cyclic minor as a determinant of row-operator values.**  Directly from
`primitiveThetaDerivativeMatrix_entry`: the cyclic consecutive `p × p` minor equals the
determinant of the matrix whose `(r,s)` entry is `A (φ_s)` evaluated at the sample point
`x_r = a + (cyclicConsecutiveRows p q j r)/q`. -/
theorem cyclic_minor_eq_rowOp_det {p q : ℕ} [NeZero q]
    (τ lam a : ℂ) (hτ : 0 < τ.im) (j : Fin q) :
    ((primitiveThetaDerivativeMatrix p q τ lam a).submatrix
        (cyclicConsecutiveRows p q j) id).det =
      (Matrix.of fun r s : Fin p =>
        rowOp lam (thetaCol p τ s)
          (a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ))).det := by
  have hmat : (primitiveThetaDerivativeMatrix p q τ lam a).submatrix
      (cyclicConsecutiveRows p q j) id =
      (Matrix.of fun r s : Fin p =>
        rowOp lam (thetaCol p τ s)
          (a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ))) := by
    ext r s
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq]
    exact (rowOp_thetaCol_eq_entry τ lam a hτ (cyclicConsecutiveRows p q j r) s).symm
  rw [hmat]

/-- The theta column functions are differentiable, packaged for `foldCoordOp_det`. -/
theorem thetaCol_diff_all {p : ℕ} {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ s, Differentiable ℂ (thetaCol p τ s) :=
  fun s => thetaCol_differentiable hτ s

/-- Each theta column is analytic on all of `ℂ`: `jacobiTheta₂(·,τ)` (analytic by the
project's `theta_analyticOnNhd`) precomposed with a translation. -/
theorem thetaCol_analyticOnNhd {p : ℕ} {τ : ℂ} (hτ : 0 < τ.im) (s : Fin p) :
    AnalyticOnNhd ℂ (thetaCol p τ s) Set.univ := by
  have hth : AnalyticOnNhd ℂ (fun z : ℂ => jacobiTheta₂ z τ) Set.univ :=
    LyubarskiiNes.FrobeniusDeterminant.ThetaZeroCount.theta_analyticOnNhd hτ
  intro z _
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + ((s : ℕ) : ℂ) / (p : ℂ)) z :=
    (analyticAt_id).add analyticAt_const
  exact (hth _ (Set.mem_univ _)).comp hshift

/-- The derivative of a theta column is analytic (hence differentiable): the derivative of
an analytic function is analytic.  This is the `C²`-type input needed by
`foldCoordOp_det`. -/
theorem thetaCol_deriv_diff_all {p : ℕ} {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ s, Differentiable ℂ (deriv (thetaCol p τ s)) := by
  intro s
  have hderiv_an : AnalyticOnNhd ℂ (deriv (thetaCol p τ s)) Set.univ :=
    (thetaCol_analyticOnNhd hτ s).deriv
  exact fun z => (hderiv_an z (Set.mem_univ z)).differentiableAt

/-- **The cyclic minor as the full coordinate operator applied to the Frobenius
determinant (STEP 1, assembled).**  Combining `cyclic_minor_eq_rowOp_det` with the
operator-through-determinant master identity `foldCoordOp_det`, the cyclic minor equals
`[∏_r A_{y_r} G](x_j)`, where `G(y) = (frobMatrix p τ y).det` and `x_j r = a + (cyclic
row)/q`.  This is exactly the object to which the F1 factorization `frobenius_factorization_probe`
is substituted in STEP 2. -/
theorem cyclic_minor_eq_foldCoordOp_frob {p q : ℕ} [NeZero q]
    (τ lam a : ℂ) (hτ : 0 < τ.im) (j : Fin q) :
    ((primitiveThetaDerivativeMatrix p q τ lam a).submatrix
        (cyclicConsecutiveRows p q j) id).det =
      foldCoordOp lam (List.finRange p)
        (fun y : Fin p → ℂ => (frobMatrix p τ y).det)
        (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) := by
  rw [cyclic_minor_eq_rowOp_det τ lam a hτ j]
  -- `frobMatrix p τ y = of fun r s => thetaCol p τ s (y r)`.
  have hfrob : (fun y : Fin p → ℂ => (frobMatrix p τ y).det) =
      (fun y : Fin p → ℂ => (Matrix.of fun r s : Fin p => thetaCol p τ s (y r)).det) := by
    funext y; rfl
  rw [hfrob, foldCoordOp_det lam (thetaCol p τ)
    (thetaCol_diff_all hτ) (thetaCol_deriv_diff_all hτ)]

/-! ## STEP 2 infrastructure — the confluent diagonal collapse (new, fully verified)

STEP 1 reduced the minor to `foldCoordOp lam (finRange p) G x` with
`G(y) = (frobMatrix p τ y).det`.  By F1, `G(y) = C · Ξ(∑ y) · V(y)`.  The genuine
analytic mechanism of STEP 2 is how the coordinate-operator fold acts on the
*diagonal* factor `Ξ(∑ y)`: because `∂_{y_r} Ξ(∑ y) = Ξ'(∑ y)` (chain rule,
coefficient `1` since `∂_{y_r}(∑ y) = 1`), each coordinate operator acts on
`Ξ(∑·)` exactly as the *univariate* operator `A = 𝔡 + λ` acts on `Ξ`, composed
with the sum.  Folding over all `p` coordinates therefore collapses `Ξ(∑·)` to the
`p`-fold iterate `(𝔡+λ)^p Ξ` evaluated at `∑ y`.  This is `foldCoordOp_diag` below,
proved sorry-free.  The product rule `coordOp_diag_mul` handles the interaction with
the `V`-factor. -/

/-- The sum over a `Function.update y r₀ t` splits as `t + (∑ over the other coords)`. -/
theorem sum_update {p : ℕ} (y : Fin p → ℂ) (r₀ : Fin p) (t : ℂ) :
    (∑ r, Function.update y r₀ t r) = t + ∑ r ∈ Finset.univ.erase r₀, y r := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r₀), Function.update_self]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]

/-- The single-coordinate scaled derivative (no `lam` term). -/
noncomputable def coordScaledDeriv {p : ℕ} (r₀ : Fin p) (W : (Fin p → ℂ) → ℂ) :
    (Fin p → ℂ) → ℂ :=
  fun y => paperDerivScale * deriv (fun t : ℂ => W (Function.update y r₀ t)) (y r₀)

/-- **Product rule for `coordOp` on a diagonal-times-`W` factorization.**  With `Φ`
differentiable and `W` slice-differentiable at every coordinate, the coordinate operator
distributes as the Leibniz product rule: it hits either the `Φ(∑·)` factor (giving
`(𝔡Φ)(∑y)·W`, chain-rule coefficient `1`) or the `W` factor (giving
`Φ(∑y)·(coordScaledDeriv r₀ W)`), plus the `lam` term.  This is the mechanism by which the
`V`-factor of the F1 factorization contributes the lower-order coefficients of the
confluent expansion. -/
theorem coordOp_diag_mul {p : ℕ} (lam : ℂ) (r₀ : Fin p) (Φ : ℂ → ℂ)
    (W : (Fin p → ℂ) → ℂ) (hΦ : Differentiable ℂ Φ)
    (hW : ∀ y, DifferentiableAt ℂ (fun t : ℂ => W (Function.update y r₀ t)) (y r₀))
    (y : Fin p → ℂ) :
    coordOp lam r₀ (fun z : Fin p → ℂ => Φ (∑ r, z r) * W z) y =
      paperDerivScale * deriv Φ (∑ r, y r) * W y
        + Φ (∑ r, y r) * coordScaledDeriv r₀ W y
        + lam * (Φ (∑ r, y r) * W y) := by
  unfold coordOp coordScaledDeriv
  set K : ℂ := ∑ r ∈ Finset.univ.erase r₀, y r with hK
  have hΦslice : (fun t : ℂ => Φ (∑ r, Function.update y r₀ t r)) =
      (fun t : ℂ => Φ (t + K)) := by
    funext t; rw [sum_update]
  have hΦderiv : HasDerivAt (fun t : ℂ => Φ (∑ r, Function.update y r₀ t r))
      (deriv Φ (∑ r, y r)) (y r₀) := by
    rw [hΦslice]
    have h1 : HasDerivAt (fun t : ℂ => t + K) 1 (y r₀) := by
      simpa using (hasDerivAt_id (y r₀)).add_const K
    have h2 : HasDerivAt Φ (deriv Φ (y r₀ + K)) (y r₀ + K) := (hΦ _).hasDerivAt
    have hsum : y r₀ + K = ∑ r, y r := by
      rw [hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ r₀)]
    have hcc : HasDerivAt (fun t : ℂ => Φ (t + K)) (deriv Φ (y r₀ + K) * 1) (y r₀) :=
      h2.comp (y r₀) h1
    rw [hsum] at hcc
    simpa using hcc
  have hWderiv : HasDerivAt (fun t : ℂ => W (Function.update y r₀ t))
      (deriv (fun t : ℂ => W (Function.update y r₀ t)) (y r₀)) (y r₀) :=
    (hW y).hasDerivAt
  have hupd : Function.update y r₀ (y r₀) = y := Function.update_eq_self r₀ y
  have hprodderiv : HasDerivAt
      (fun t : ℂ => Φ (∑ r, Function.update y r₀ t r) * W (Function.update y r₀ t))
      (deriv Φ (∑ r, y r) * W y
        + Φ (∑ r, y r) * deriv (fun t : ℂ => W (Function.update y r₀ t)) (y r₀)) (y r₀) := by
    have hmul := hΦderiv.mul hWderiv
    have hmul' : HasDerivAt
        (fun t : ℂ => Φ (∑ r, Function.update y r₀ t r) * W (Function.update y r₀ t))
        (deriv Φ (∑ r, y r) * W (Function.update y r₀ (y r₀))
          + Φ (∑ r, Function.update y r₀ (y r₀) r) *
            deriv (fun t : ℂ => W (Function.update y r₀ t)) (y r₀)) (y r₀) := hmul
    rw [hupd] at hmul'
    exact hmul'
  rw [hprodderiv.deriv]
  ring

/-! ## STEP 2 bridge — `iterRowOp` as an operator polynomial (new, fully verified)

The diagonal collapse `foldCoordOp_diag` produces `iterRowOp lam p Ξ = (𝔡+λ)^p Ξ`.  To land
in the target's `polynomialScaledDeriv P Ξ` form we prove the binomial identity
`(𝔡+λ)^n = ∑_{k≤n} C(n,k) λ^{n-k} 𝔡^k`, then package it as
`polynomialScaledDeriv ((X + C λ)^n)`.  This is exactly the constant-`V` skeleton of the
confluent expansion, now fully verified: with `V ≡ v` constant, F1 gives
`G(y) = (C·v)·Ξ(∑y)` and `foldCoordOp_diag` + this bridge deliver
`minor = (C·v)·polynomialScaledDeriv (rowOpPoly λ p) Ξ (∑ x)`, a degree-`p` operator
polynomial with nonzero leading coefficient.  (The genuine `V`-non-constant corrections are
what remain in the residual.) -/

theorem contDiff_iterScaledDeriv (Φ : ℂ → ℂ) (hΦ : ContDiff ℂ ∞ Φ) :
    ∀ k, ContDiff ℂ ∞ (iterScaledDeriv k Φ) := by
  intro k
  induction k with
  | zero => simpa [iterScaledDeriv] using hΦ
  | succ n ih =>
      simp only [iterScaledDeriv]; unfold scaledDeriv
      have := (contDiff_infty_iff_deriv.mp ih).2
      have h1 : ContDiff ℂ ∞ (fun z => paperDerivScale * deriv (iterScaledDeriv n Φ) z) := by
        have := this.const_smul (c := paperDerivScale); simpa only [smul_eq_mul] using this
      exact h1

-- scaledDeriv of a finite sum of (const * smooth) distributes.
namespace Bridge2
open Polynomial LyubarskiiNes.TorsionJets

end Bridge2

/-- `XiSection p (pτ)` is `C^∞` (it is analytic on all of `ℂ`). -/
theorem contDiff_XiSection {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) :
    ContDiff ℂ ∞ (XiSection p ((p : ℂ) * τ)) := by
  have hΩ : 0 < ((p : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_im, Complex.natCast_re, zero_mul, add_zero]
    positivity
  exact (XiSection_analyticOnNhd p ((p : ℂ) * τ) hΩ).contDiff

/-! ## STEP 2 — the non-constant-`V` confluent Leibniz collapse (κ-induction)

`foldCoordOp_diag_poly` closed the *constant-`V`* skeleton.  The genuine content of STEP 2
is the interaction of the operator fold with the full `V`-factor.  We prove the confluent
Leibniz **invariant**: folding the coordinate operators over a list `L` applied to the
diagonal-times-`V` function `y ↦ Ξ(∑y)·V(y)` produces a finite sum
`∑_{k=0}^{|L|} κ_k(y) · (𝔡^k Ξ)(∑y)`, where the coefficient functions `κ_k` are again
`C^∞`, the leading coefficient `κ_{|L|} = V`, and the recursion under prepending a
coordinate `r₀` is `κ'_m = coordOp lam r₀ (κ_m) + κ_{m-1}` (`κ_{-1} := 0`).  The derivative
hitting the `𝔡^k Ξ` factor raises `k` by one (chain-rule coefficient `1` from
`∂_{y_r}(∑y)=1`); the derivative hitting `κ_m` gives the `coordOp`-recursion.

The `C^∞` bookkeeping is handled uniformly via the `fderiv`-slice identity: the coordinate
slice-derivative equals `fderiv` applied to a unit vector, which is `C^∞` when the base
function is. -/

/-- Slice of a `ContDiff` multivariable function is `ContDiff`. -/
theorem contDiff_slice {p : ℕ} (W : (Fin p → ℂ) → ℂ) (hW : ContDiff ℂ ∞ W)
    (y : Fin p → ℂ) (r₀ : Fin p) :
    ContDiff ℂ ∞ (fun t : ℂ => W (Function.update y r₀ t)) :=
  hW.comp (contDiff_update ∞ y r₀)

/-- The coordinate slice-derivative equals the `fderiv` applied to the unit vector
`Pi.single r₀ 1`.  This is the key identity that gives uniform `C^∞`-preservation of the
coordinate operators. -/
theorem coordSliceDeriv_eq_fderiv {p : ℕ} (W : (Fin p → ℂ) → ℂ) (hW : ContDiff ℂ ∞ W)
    (y : Fin p → ℂ) (r₀ : Fin p) :
    deriv (fun t : ℂ => W (Function.update y r₀ t)) (y r₀) =
      fderiv ℂ W y (Pi.single r₀ (1 : ℂ)) := by
  have hup : HasDerivAt (Function.update y r₀) (Pi.single r₀ (1 : ℂ)) (y r₀) :=
    hasDerivAt_update y r₀ (y r₀)
  have hupeq : Function.update y r₀ (y r₀) = y := Function.update_eq_self r₀ y
  have hWd : HasFDerivAt W (fderiv ℂ W y) (Function.update y r₀ (y r₀)) := by
    rw [hupeq]; exact (hW.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasDerivAt (W ∘ Function.update y r₀)
      (fderiv ℂ W y (Pi.single r₀ (1 : ℂ))) (y r₀) := by
    have := hWd.comp_hasDerivAt (y r₀) hup
    simpa using this
  exact hcomp.deriv

/-- `y ↦ fderiv ℂ W y v` is `ContDiff` for a fixed vector `v`. -/
theorem contDiff_fderiv_const_apply {p : ℕ} (W : (Fin p → ℂ) → ℂ) (hW : ContDiff ℂ ∞ W)
    (v : Fin p → ℂ) :
    ContDiff ℂ ∞ (fun y : Fin p → ℂ => fderiv ℂ W y v) :=
  ((contDiff_infty_iff_fderiv.mp hW).2).clm_apply contDiff_const

/-- `coordScaledDeriv r₀ W` is `ContDiff ℂ ∞` when `W` is. -/
theorem contDiff_coordScaledDeriv {p : ℕ} (r₀ : Fin p) (W : (Fin p → ℂ) → ℂ)
    (hW : ContDiff ℂ ∞ W) :
    ContDiff ℂ ∞ (coordScaledDeriv r₀ W) := by
  have heq : coordScaledDeriv r₀ W =
      fun y : Fin p → ℂ => paperDerivScale * fderiv ℂ W y (Pi.single r₀ (1 : ℂ)) := by
    funext y
    unfold coordScaledDeriv
    rw [coordSliceDeriv_eq_fderiv W hW y r₀]
  rw [heq]
  have := (contDiff_fderiv_const_apply W hW (Pi.single r₀ (1 : ℂ))).const_smul
    (c := paperDerivScale)
  simpa only [smul_eq_mul] using this

/-- `coordOp lam r₀ W` is `ContDiff ℂ ∞` when `W` is. -/
theorem contDiff_coordOp {p : ℕ} (lam : ℂ) (r₀ : Fin p) (W : (Fin p → ℂ) → ℂ)
    (hW : ContDiff ℂ ∞ W) :
    ContDiff ℂ ∞ (coordOp lam r₀ W) := by
  have heq : coordOp lam r₀ W = fun y => coordScaledDeriv r₀ W y + lam * W y := by
    funext y; rfl
  rw [heq]
  have h1 : ContDiff ℂ ∞ (coordScaledDeriv r₀ W) := contDiff_coordScaledDeriv r₀ W hW
  have h2 : ContDiff ℂ ∞ (fun y : Fin p → ℂ => lam * W y) := by
    have := hW.const_smul (c := lam); simpa only [smul_eq_mul] using this
  exact h1.add h2

/-- A `ContDiff ℂ ∞` function is `SliceDiff` (every coordinate slice is differentiable). -/
theorem sliceDiff_of_contDiff {p : ℕ} (W : (Fin p → ℂ) → ℂ) (hW : ContDiff ℂ ∞ W) :
    SliceDiff W := by
  intro r₀ y
  exact ((contDiff_slice W hW y r₀).differentiable (by simp)).differentiableAt

/-- The coordinate-sum `z ↦ ∑ r, z r` is `ContDiff ℂ ∞` (a continuous linear map). -/
theorem contDiff_coordSum {p : ℕ} : ContDiff ℂ ∞ (fun z : Fin p → ℂ => ∑ r, z r) :=
  ContDiff.sum (fun i _ => contDiff_apply ℂ ℂ i)

/-- `SliceDiff` is closed under finite sums. -/
theorem sliceDiff_finset_sum {p : ℕ} {ι : Type*} (s : Finset ι) (G : ι → (Fin p → ℂ) → ℂ)
    (hG : ∀ i ∈ s, SliceDiff (G i)) :
    SliceDiff (fun z : Fin p → ℂ => ∑ i ∈ s, G i z) := by
  intro r₀ y
  have heq : (fun t : ℂ => ∑ i ∈ s, G i (Function.update y r₀ t)) =
      fun t : ℂ => ∑ i ∈ s, (fun t : ℂ => G i (Function.update y r₀ t)) t := rfl
  rw [show (fun t : ℂ => (fun z : Fin p → ℂ => ∑ i ∈ s, G i z) (Function.update y r₀ t))
      = fun t : ℂ => ∑ i ∈ s, G i (Function.update y r₀ t) from rfl]
  exact DifferentiableAt.fun_sum (fun i hi => hG i hi r₀ y)

/-- **The confluent Leibniz κ-invariant (STEP 2 heart).**  Folding the coordinate operators
over a list `l` applied to the diagonal-times-`V` function `y ↦ Ξ(∑y)·V(y)` yields a finite
`𝔡`-jet expansion `∑_{k=0}^{|l|} κ_k(y)·(𝔡^k Ξ)(∑y)` with `C^∞` coefficient functions `κ_k`,
vanishing above level `|l|`, and leading coefficient `κ_{|l|} = V`.  Proved by induction on
`l` from the verified product rule `coordOp_diag_mul` and additivity `coordOp_add`. -/
theorem foldCoordOp_kappa_invariant {p : ℕ} (lam : ℂ) (Ξ : ℂ → ℂ) (V : (Fin p → ℂ) → ℂ)
    (hΞ : ContDiff ℂ ∞ Ξ) (hV : ContDiff ℂ ∞ V) (l : List (Fin p)) :
    ∃ κ : ℕ → (Fin p → ℂ) → ℂ,
      (∀ k, ContDiff ℂ ∞ (κ k)) ∧
      (∀ k, l.length < k → κ k = 0) ∧
      κ l.length = V ∧
      (∀ (w : Fin p → ℂ) (c : ℂ),
        (∀ y, V (fun i => y i + w i) = c * V y) →
          (∀ k y, κ k (fun i => y i + w i) = c * κ k y)) ∧
      foldCoordOp lam l (fun y : Fin p → ℂ => Ξ (∑ r, y r) * V y) =
        fun y : Fin p → ℂ =>
          ∑ k ∈ Finset.range (l.length + 1), κ k y * iterScaledDeriv k Ξ (∑ r, y r) := by
  induction l with
  | nil =>
      refine ⟨fun k => if k = 0 then V else 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; by_cases hk : k = 0
        · simp only [hk, if_pos]; exact hV
        · simp only [if_neg hk]; exact contDiff_const
      · intro k hk; simp only [List.length_nil] at hk; simp only [if_neg (by omega : k ≠ 0)]
      · show (if (0:ℕ) = 0 then V else 0) = V
        rw [if_pos rfl]
      · -- covariance: κ 0 = V (use hw); κ k = 0 for k ≠ 0 (trivial).
        intro w c hw k y
        by_cases hk : k = 0
        · simp only [hk, if_pos]; exact hw y
        · simp only [if_neg hk, Pi.zero_apply, mul_zero]
      · funext y
        show Ξ (∑ r, y r) * V y
          = ∑ x ∈ Finset.range 1, (if x = 0 then V else 0) y * iterScaledDeriv x Ξ (∑ r, y r)
        rw [Finset.sum_range_one]
        simp only [if_pos, iterScaledDeriv]
        ring
  | cons a t ih =>
      obtain ⟨κ, hκcd, hκvanish, hκlead, hκcov, hκeq⟩ := ih
      -- New coefficient functions after prepending coordinate `a`.
      set κ' : ℕ → (Fin p → ℂ) → ℂ :=
        fun m => fun y => coordOp lam a (κ m) y + (if m = 0 then 0 else κ (m - 1) y) with hκ'
      refine ⟨κ', ?_, ?_, ?_, ?_, ?_⟩
      · -- ContDiff of each κ'_m.
        intro m
        have h1 : ContDiff ℂ ∞ (coordOp lam a (κ m)) := contDiff_coordOp lam a (κ m) (hκcd m)
        by_cases hm : m = 0
        · have heq : κ' m = coordOp lam a (κ m) := by
            funext y; simp only [hκ', hm, if_pos]; ring
          rw [heq]; exact h1
        · have heq : κ' m = fun y => coordOp lam a (κ m) y + κ (m - 1) y := by
            funext y; simp only [hκ', if_neg hm]
          rw [heq]; exact h1.add (hκcd (m - 1))
      · -- vanishing above the new length.
        intro k hk
        simp only [List.length_cons] at hk
        have hkt : t.length < k := by omega
        have hktm : t.length < k - 1 := by omega
        funext y
        simp only [hκ']
        have e1 : κ k = 0 := hκvanish k hkt
        have e2 : coordOp lam a (κ k) = coordOp lam a 0 := by rw [e1]
        rw [show coordOp lam a (κ k) y = coordOp lam a (0 : (Fin p → ℂ) → ℂ) y from
          congrFun e2 y]
        have hz0 : coordOp lam a (0 : (Fin p → ℂ) → ℂ) = 0 := coordOp_zero lam a
        rw [show coordOp lam a (0 : (Fin p → ℂ) → ℂ) y = 0 from congrFun hz0 y]
        have hkne : k ≠ 0 := by omega
        simp only [if_neg hkne, hκvanish (k - 1) hktm, Pi.zero_apply]
        ring
      · -- leading coefficient at new length = V.
        show κ' (t.length + 1) = V
        funext y
        have hne : t.length + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [hκ', if_neg hne, Nat.add_sub_cancel]
        have e1 : κ (t.length + 1) = 0 := hκvanish (t.length + 1) (by omega)
        rw [show coordOp lam a (κ (t.length + 1)) y
            = coordOp lam a (0 : (Fin p → ℂ) → ℂ) y from by rw [e1]]
        rw [show coordOp lam a (0 : (Fin p → ℂ) → ℂ) y = 0 from congrFun (coordOp_zero lam a) y]
        rw [hκlead]; ring
      · -- covariance of κ' inherited from covariance of κ.
        intro w c hw k y
        -- κ' k = coordOp lam a (κ k) + (if k=0 then 0 else κ (k-1)).
        -- Covariance of κ (from IH) makes `fun y => κ m (y+w) = fun y => c * κ m y`.
        have hcovk : ∀ m, (fun y : Fin p → ℂ => κ m (fun i => y i + w i))
            = fun y : Fin p → ℂ => c * κ m y := by
          intro m; funext z; exact hκcov w c hw m z
        -- Push `c` through coordOp: coordOp lam a (κ m) (y+w) = c * coordOp lam a (κ m) y.
        have hcoord : ∀ m, coordOp lam a (κ m) (fun i => y i + w i)
            = c * coordOp lam a (κ m) y := by
          intro m
          have h1 : coordOp lam a (fun y : Fin p → ℂ => κ m (fun i => y i + w i))
              = fun y : Fin p → ℂ => (coordOp lam a (κ m)) (fun i => y i + w i) :=
            coordOp_comp_add_const lam a (κ m) w
          have h2 : coordOp lam a (fun y : Fin p → ℂ => κ m (fun i => y i + w i))
              = coordOp lam a (fun y : Fin p → ℂ => c • κ m y) := by
            rw [hcovk m]; simp only [smul_eq_mul]
          have h3 : coordOp lam a (fun y : Fin p → ℂ => c • κ m y)
              = fun y : Fin p → ℂ => c • coordOp lam a (κ m) y :=
            coordOp_smul lam a c (κ m)
          have := congrFun (h1.symm.trans (h2.trans h3)) y
          simpa only [smul_eq_mul] using this
        simp only [hκ']
        by_cases hk : k = 0
        · simp only [hk, if_pos]; rw [hcoord 0]; ring
        · simp only [if_neg hk]
          rw [hcoord k, hκcov w c hw (k - 1) y]; ring
      · -- the fold identity.
        funext y
        have hfoldstep : foldCoordOp lam (a :: t)
            (fun z : Fin p → ℂ => Ξ (∑ r, z r) * V z) =
            coordOp lam a (foldCoordOp lam t (fun z : Fin p → ℂ => Ξ (∑ r, z r) * V z)) := by
          simp only [foldCoordOp, List.foldr_cons]
        rw [hfoldstep, hκeq]
        -- Apply coordOp to the finite sum via additivity + product rule per term.
        -- First: coordOp distributes over the finite sum.
        set n := t.length with hn
        -- Each summand is a diagonal-times-W product; SliceDiff for additivity.
        have hcd_iterΞ : ∀ k, ContDiff ℂ ∞ (iterScaledDeriv k Ξ) :=
          contDiff_iterScaledDeriv Ξ hΞ
        -- Rewrite each summand `κ k · iterΞ_k(∑·)` as `iterΞ_k(∑·) · κ k` for coordOp_diag_mul.
        have hterm : ∀ k : ℕ,
            coordOp lam a (fun z : Fin p → ℂ => κ k z * iterScaledDeriv k Ξ (∑ r, z r)) =
              fun y => coordOp lam a (κ k) y * iterScaledDeriv k Ξ (∑ r, y r)
                + κ k y * iterScaledDeriv (k + 1) Ξ (∑ r, y r) := by
          intro k
          funext y
          have hcomm : (fun z : Fin p → ℂ => κ k z * iterScaledDeriv k Ξ (∑ r, z r)) =
              (fun z : Fin p → ℂ => iterScaledDeriv k Ξ (∑ r, z r) * κ k z) := by
            funext z; ring
          rw [hcomm]
          have hΦ : Differentiable ℂ (iterScaledDeriv k Ξ) := (hcd_iterΞ k).differentiable (by simp)
          have hW : ∀ y, DifferentiableAt ℂ
              (fun t : ℂ => κ k (Function.update y a t)) (y a) := fun y =>
            (sliceDiff_of_contDiff (κ k) (hκcd k)) a y
          rw [coordOp_diag_mul lam a (iterScaledDeriv k Ξ) (κ k) hΦ hW y]
          -- coordScaledDeriv a (κ k) + λ·κ k = coordOp lam a (κ k), and 𝔡(iterΞ_k)=iterΞ_{k+1}.
          have hcs : coordOp lam a (κ k) y
              = coordScaledDeriv a (κ k) y + lam * κ k y := rfl
          have hderiv : paperDerivScale * deriv (iterScaledDeriv k Ξ) (∑ r, y r)
              = iterScaledDeriv (k + 1) Ξ (∑ r, y r) := by
            simp only [iterScaledDeriv, scaledDeriv]
          rw [hcs, hderiv]
          ring
        -- Additivity of coordOp over the finite sum.
        have hadd : coordOp lam a (fun z : Fin p → ℂ =>
              ∑ k ∈ Finset.range (n + 1), κ k z * iterScaledDeriv k Ξ (∑ r, z r)) y
            = ∑ k ∈ Finset.range (n + 1),
                coordOp lam a (fun z : Fin p → ℂ =>
                  κ k z * iterScaledDeriv k Ξ (∑ r, z r)) y := by
          -- prove the functional form by induction over the finset
          have hSD : ∀ k, SliceDiff (fun z : Fin p → ℂ =>
              κ k z * iterScaledDeriv k Ξ (∑ r, z r)) := by
            intro k
            apply sliceDiff_of_contDiff
            have hd : ContDiff ℂ ∞ (fun z : Fin p → ℂ => iterScaledDeriv k Ξ (∑ r, z r)) :=
              (hcd_iterΞ k).comp contDiff_coordSum
            exact (hκcd k).mul hd
          -- distribute via a finset induction using coordOp_add
          have hdistrib : ∀ (s : Finset ℕ),
              coordOp lam a (fun z : Fin p → ℂ =>
                ∑ k ∈ s, κ k z * iterScaledDeriv k Ξ (∑ r, z r))
              = fun y => ∑ k ∈ s, coordOp lam a (fun z : Fin p → ℂ =>
                  κ k z * iterScaledDeriv k Ξ (∑ r, z r)) y := by
            intro s
            induction s using Finset.induction with
            | empty =>
                funext y
                simp only [Finset.sum_empty]
                exact congrFun (coordOp_zero lam a) y
            | insert b s hb ih2 =>
                have hsplit : (fun z : Fin p → ℂ =>
                    ∑ k ∈ insert b s, κ k z * iterScaledDeriv k Ξ (∑ r, z r)) =
                    (fun z : Fin p → ℂ =>
                      (κ b z * iterScaledDeriv b Ξ (∑ r, z r))
                        + ∑ k ∈ s, κ k z * iterScaledDeriv k Ξ (∑ r, z r)) := by
                  funext z; rw [Finset.sum_insert hb]
                rw [hsplit]
                have hSDsum : SliceDiff (fun z : Fin p → ℂ =>
                    ∑ k ∈ s, κ k z * iterScaledDeriv k Ξ (∑ r, z r)) :=
                  sliceDiff_finset_sum s _ (fun k _ => hSD k)
                rw [coordOp_add lam a _ _ (hSD b) hSDsum]
                funext yy
                rw [Finset.sum_insert hb, congrFun ih2 yy]
          rw [congrFun (hdistrib (Finset.range (n+1))) y]
        rw [hadd]
        -- now substitute per-term identity and apply the sum reindex identity.
        have hsum : ∑ k ∈ Finset.range (n + 1),
              coordOp lam a (fun z : Fin p → ℂ =>
                κ k z * iterScaledDeriv k Ξ (∑ r, z r)) y
            = ∑ k ∈ Finset.range (n + 1),
                (coordOp lam a (κ k) y * iterScaledDeriv k Ξ (∑ r, y r)
                  + κ k y * iterScaledDeriv (k + 1) Ξ (∑ r, y r)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [congrFun (hterm k) y]
        rw [hsum]
        -- Apply the pure sum reindex identity with d k = coordOp(κ k) y, a k = κ k y,
        -- F k = iterScaledDeriv k Ξ (∑ y).  Need d (n+1) = 0.
        set d : ℕ → ℂ := fun k => coordOp lam a (κ k) y with hd_def
        set av : ℕ → ℂ := fun k => κ k y with hav
        set F : ℕ → ℂ := fun k => iterScaledDeriv k Ξ (∑ r, y r) with hF
        have hdn1 : d (n + 1) = 0 := by
          simp only [hd_def]
          have e1 : κ (n + 1) = 0 := hκvanish (n + 1) (by omega)
          rw [show coordOp lam a (κ (n+1)) y = coordOp lam a (0 : (Fin p → ℂ) → ℂ) y from by
            rw [e1]]
          exact congrFun (coordOp_zero lam a) y
        have hreindex : (∑ k ∈ Finset.range (n+1), (d k * F k + av k * F (k+1)))
            = ∑ m ∈ Finset.range (n+2),
                ((d m) + (if m = 0 then 0 else av (m-1))) * F m := by
          have hL : (∑ k ∈ Finset.range (n+1), (d k * F k + av k * F (k+1)))
              = (∑ k ∈ Finset.range (n+1), d k * F k)
                + (∑ k ∈ Finset.range (n+1), av k * F (k+1)) := by
            rw [Finset.sum_add_distrib]
          rw [hL]
          have hR : (∑ m ∈ Finset.range (n+2),
                ((d m) + (if m = 0 then 0 else av (m-1))) * F m)
              = (∑ m ∈ Finset.range (n+2), d m * F m)
                + (∑ m ∈ Finset.range (n+2), (if m = 0 then 0 else av (m-1)) * F m) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun m _ => by ring)
          rw [hR]
          have h1 : (∑ m ∈ Finset.range (n+2), d m * F m)
              = ∑ k ∈ Finset.range (n+1), d k * F k := by
            rw [Finset.sum_range_succ, hdn1]; ring
          have h2 : (∑ m ∈ Finset.range (n+2), (if m = 0 then 0 else av (m-1)) * F m)
              = ∑ k ∈ Finset.range (n+1), av k * F (k+1) := by
            rw [Finset.sum_range_succ'
              (fun m => (if m = 0 then 0 else av (m-1)) * F m) (n+1)]; simp
          rw [h1, h2]
        -- massage LHS into d*F + av*F(k+1) form
        have hLHS : (∑ k ∈ Finset.range (n + 1),
              (coordOp lam a (κ k) y * iterScaledDeriv k Ξ (∑ r, y r)
                + κ k y * iterScaledDeriv (k + 1) Ξ (∑ r, y r)))
            = ∑ k ∈ Finset.range (n+1), (d k * F k + av k * F (k+1)) := by
          refine Finset.sum_congr rfl (fun k _ => by simp only [hd_def, hav, hF])
        rw [hLHS, hreindex]
        -- RHS target: ∑_{m ∈ range((a::t).length+1)} κ' m y * iterΞ_m(∑y).
        -- Termwise: κ' m y = d m + (if m=0 then 0 else av (m-1)); the two sums agree.
        have hlen : (a :: t).length + 1 = n + 2 := by simp only [List.length_cons, hn]
        have hterms : (∑ m ∈ Finset.range (n+2),
              ((d m) + (if m = 0 then 0 else av (m-1))) * F m)
            = ∑ m ∈ Finset.range (n+2),
                κ' m y * iterScaledDeriv m Ξ (∑ r, y r) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          simp only [hκ', hd_def, hav, hF, Pi.add_apply]
        rw [hlen, hterms]

/-! ## STEP 2/3 residual and the target theorem

STEP 1 above reduces the cyclic minor `M_j` to `[∏_r A_{y_r} G](x_j)` with
`G(y) = (frobMatrix p τ y).det` and `x_j r = a + (cyclicConsecutiveRows p q j r)/q`.  What
remains — STEP 2/3 — is the genuine analytic content:

* **STEP 2 (confluent Leibniz collapse).**  Substitute F1
  (`frobenius_factorization_probe`): `G(y) = C·Ξ(∑y)·V(y)` with
  `Ξ = XiSection p (pτ)`, `V(y) = ∏_{r<s} oddTheta (pτ) (y_s − y_r)`.  Because `Ξ(∑y)`
  depends on `y` only through `σ = ∑ y` and, at the arithmetic-progression config `x_j`,
  the `V`-factors and their `y`-derivatives are *constants* (differences `(x_s − x_r)`
  are `j`-independent residues), the generalized Leibniz expansion of `∏_r A_{y_r}`
  collapses to a polynomial `∑_k a_k · iterScaledDeriv k Ξ (∑ x_j)` with the `a_k`
  *independent of `j`* and leading coefficient `a_p = V(x_j) ≠ 0`
  (`oddTheta_consecutive_product_ne_zero`).
* **STEP 3 (argument reindexing).**  `∑ x_j = p·(b + j/q)` for a `j`-independent `b`,
  via the coprime cyclic residue-sum identity.

Both steps require multivariable calculus (iterated derivatives of `Ξ(∑y)·V(y)` through
the operator fold) that is not yet formalized here.  We package their conjunction as the
single residual `minor_polynomial_data`, from which the target follows by pure algebra +
STEP 1.  The residual is stated so that its `polynomialScaledDeriv` conclusion is literally
the target's right-hand side. -/

/-! **STEP 2/3 residual (single labelled blocker).**  The confluent Leibniz collapse of
the STEP-1 operator applied to the F1 factorization, together with the STEP-3 argument
reindexing.  Produces the polynomial `P` (degree `p`, `≠ 0`), the base point `b`, and the
nonzero scalars `c j`, with the operator identity in `polynomialScaledDeriv` form.  This is
exactly the paper's Steps 2–3; STEP 1 (`cyclic_minor_eq_foldCoordOp_frob`) has already
turned the left-hand side into `[∏_r A_{y_r} G](x_j)`.

REDUCTION PATH now available (this file adds the verified mechanism):

* Substitute `frobenius_factorization_probe`: `G(y) = C·Ξ(∑y)·V(y)` with
  `Ξ = XiSection p (pτ)`, `V(y) = ∏_{r<s} oddTheta (pτ) (y_s − y_r)`.
* `foldCoordOp_diag` (verified) handles the *constant-`V`* skeleton exactly: it collapses
  `Ξ(∑·)` under the fold to `iterRowOp lam p Ξ (∑ y) = (𝔡+λ)^p Ξ (∑ y)`, which is a
  degree-`p` operator polynomial in `𝔡` applied to `Ξ`.
* `coordOp_diag_mul` (verified) is the product rule that peels the `V`-factor: each
  coordinate operator produces `(𝔡Ξ)(∑y)·W + Ξ(∑y)·(𝔡_{r₀}W) + λ·Ξ(∑y)·W`.  Folding this
  recursively over the `p` coordinates expands into `2^p` terms, each a product of some
  `Ξ^{(k)}(∑y)` with a mixed `V`-partial; at the AP config `x_j` those `V`-partials are
  `j`-independent constants (they depend only on the residue differences), yielding the
  `j`-independent coefficients `a_k` with leading `a_p = C·V(x_j) ≠ 0`
  (`oddTheta_consecutive_product_ne_zero`).

The `iterRowOp ↔ polynomialScaledDeriv` binomial bridge
`(𝔡+λ)^n = polynomialScaledDeriv ((X+C λ)^n)` is now ALSO verified
(`Bridge2.iterRowOp_eq_polynomialScaledDeriv`), and the *constant-`V`* skeleton is fully
closed in target form by `foldCoordOp_diag_poly`.  The remaining formalization is therefore
exactly: (ii) the recursive `coordOp_diag_mul` expansion of the *non-constant* `V`-factor
into the `Ξ^{(k)}·const` basis with `j`-independent constants (a `2^p`-term multivariable
Leibniz over the verified `coordOp_diag`/`coordOp_diag_mul` mechanism); and (iii) the STEP-3
argument identity `∑ x_j = p·(b + j/q)` via the coprime cyclic residue-sum
(`forall_mul_coprime_iff`) — arithmetic. -/
/-- The `V`-factor of the F1 factorization is `ContDiff ℂ ∞` (a finite product of
`oddTheta`-compositions, each analytic). -/
theorem contDiff_Vfactor {p : ℕ} (hp : 0 < p) {τ : ℂ} (hτ : 0 < τ.im) :
    ContDiff ℂ ∞ (fun u : Fin p → ℂ =>
      ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
        LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)) := by
  have hΩ : 0 < ((p : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_im, Complex.natCast_re, zero_mul, add_zero]
    positivity
  have hodd : ContDiff ℂ ∞ (fun z : ℂ => LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) z) :=
    (oddTheta_analyticOnNhd ((p : ℂ) * τ) hΩ).contDiff
  apply contDiff_prod
  intro r _
  apply contDiff_prod
  intro s _
  have hlin : ContDiff ℂ ∞ (fun u : Fin p → ℂ => u s - u r) :=
    (contDiff_apply ℂ ℂ s).sub (contDiff_apply ℂ ℂ r)
  exact hodd.comp hlin

/-- **Verified STEP-2 reduction — the minor as a `C·κ`-jet.**  Substituting the F1
factorization `det = C·Ξ(∑·)·V` into the STEP-1 fold and applying the confluent Leibniz
κ-invariant, the cyclic minor becomes `C · ∑_{k=0}^{p} κ_k(x_j) · (𝔡^k Ξ)(∑ x_j)` with the
verified `C^∞` coefficient functions `κ_k` (`κ_p = V`).  This closes STEP 2 completely; only
the STEP-3 `j`-independence + argument-reindexing packaging into a single polynomial `P`,
base point `b`, and scalars `c_j` remains (see `minor_polynomial_data`). -/
theorem minor_kappa_form {p q : ℕ} [NeZero q]
    (hp : 0 < p) (τ a lam : ℂ) (hτ : 0 < τ.im) :
    ∃ (C : ℂ) (κ : ℕ → (Fin p → ℂ) → ℂ),
      C ≠ 0 ∧ (∀ k, ContDiff ℂ ∞ (κ k)) ∧
      (∀ k, p < k → κ k = 0) ∧
      κ p = (fun u : Fin p → ℂ =>
        ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)) ∧
      (∀ (w : Fin p → ℂ) (cc : ℂ),
        (∀ y : Fin p → ℂ,
          (∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) ((y s + w s) - (y r + w r)))
            = cc * ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (y s - y r)) →
          (∀ k y, κ k (fun i => y i + w i) = cc * κ k y)) ∧
      (∀ j : Fin q,
        foldCoordOp lam (List.finRange p)
          (fun y : Fin p → ℂ => (frobMatrix p τ y).det)
          (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) =
          C * ∑ k ∈ Finset.range (p + 1),
            κ k (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) *
              iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
                (∑ r, (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ)
                  / (q : ℂ)) r)) := by
  classical
  obtain ⟨C, hC0, hCeq⟩ := frobenius_factorization_probe hp τ hτ
  set Ξ : ℂ → ℂ := XiSection p ((p : ℂ) * τ) with hΞdef
  set V : (Fin p → ℂ) → ℂ := fun u : Fin p → ℂ =>
    ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
      LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r) with hVdef
  have hΞcd : ContDiff ℂ ∞ Ξ := contDiff_XiSection hp hτ
  have hVcd : ContDiff ℂ ∞ V := contDiff_Vfactor hp hτ
  obtain ⟨κ, hκcd, hκvanish, hκlead, hκcov, hκeq⟩ :=
    foldCoordOp_kappa_invariant lam Ξ V hΞcd hVcd (List.finRange p)
  rw [List.length_finRange] at hκvanish hκlead hκeq
  refine ⟨C, κ, hC0, hκcd, hκvanish, hκlead, ?_, fun j => ?_⟩
  · -- covariance conjunct: repackage `hκcov` (stated with `V`) in the unfolded form.
    intro w cc hVcov k y
    refine hκcov w cc ?_ k y
    intro z
    have := hVcov z
    simpa only [hVdef] using this
  -- Substitute F1 factorization inside the fold.
  have hGeq : (fun y : Fin p → ℂ => (frobMatrix p τ y).det) =
      fun y : Fin p → ℂ => C • (Ξ (∑ r, y r) * V y) := by
    funext y
    rw [hCeq y]
    simp only [hΞdef, hVdef, smul_eq_mul]
    ring
  rw [hGeq, foldCoordOp_smul lam (List.finRange p) C
    (fun y : Fin p → ℂ => Ξ (∑ r, y r) * V y)]
  show C • foldCoordOp lam (List.finRange p)
      (fun y : Fin p → ℂ => Ξ (∑ r, y r) * V y)
      (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) = _
  rw [congrFun hκeq (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)),
    smul_eq_mul]

/-! ## STEP 3 — translation covariance of the scaled-derivative operator (verified)

The following block (imported verbatim from the verified STEP-3 fragment of attempt #2) is
the fully-verified algebraic engine of STEP 3.  It shows that the normalized differential
operator `𝔡 = (2πi)⁻¹ d/dz`, its iterates, and the polynomial operator
`polynomialScaledDeriv P` all commute with translation of the argument, and that
`polynomialScaledDeriv P Ξ` is *integer-shift covariant with a sign*: shifting the argument
by a natural number `n` multiplies the value by `((-1)^{p+1})^n`.  This is precisely the
mechanism by which the integer part `n_j` of the argument `∑ x_j` factors out of the
`polynomialScaledDeriv` (via `XiSection_add_one`), leaving the residue argument `b + j/q`.
Nothing here is axiomatic; it is closed `sorry`-free. -/

namespace Step3

/-- `𝔡` commutes with translation: `𝔡(f(·+c)) = (𝔡 f)(·+c)`. -/
theorem scaledDeriv_comp_add_const (f : ℂ → ℂ) (c : ℂ) :
    LyubarskiiNes.TorsionJets.scaledDeriv (fun w => f (w + c))
      = fun z => LyubarskiiNes.TorsionJets.scaledDeriv f (z + c) := by
  funext z; unfold LyubarskiiNes.TorsionJets.scaledDeriv; rw [deriv_comp_add_const]

/-- The `k`-th iterate `𝔡ᵏ` commutes with translation. -/
theorem iterScaledDeriv_comp_add_const (k : ℕ) (f : ℂ → ℂ) (c : ℂ) :
    LyubarskiiNes.TorsionJets.iterScaledDeriv k (fun w => f (w + c))
      = fun z => LyubarskiiNes.TorsionJets.iterScaledDeriv k f (z + c) := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [LyubarskiiNes.TorsionJets.iterScaledDeriv, ih, LyubarskiiNes.TorsionJets.iterScaledDeriv,
        scaledDeriv_comp_add_const]

/-- The polynomial operator `P(𝔡)` commutes with translation. -/
theorem polynomialScaledDeriv_comp_add_const (P : Polynomial ℂ) (f : ℂ → ℂ) (c : ℂ) :
    LyubarskiiNes.TorsionJets.polynomialScaledDeriv P (fun w => f (w + c))
      = fun z => LyubarskiiNes.TorsionJets.polynomialScaledDeriv P f (z + c) := by
  funext z; unfold LyubarskiiNes.TorsionJets.polynomialScaledDeriv
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [iterScaledDeriv_comp_add_const]

/-- The polynomial operator `P(𝔡)` pulls a constant scalar out of its argument function. -/
theorem polynomialScaledDeriv_const_mul (P : Polynomial ℂ) (κ : ℂ) (f : ℂ → ℂ) :
    LyubarskiiNes.TorsionJets.polynomialScaledDeriv P (fun w => κ * f w)
      = fun z => κ * LyubarskiiNes.TorsionJets.polynomialScaledDeriv P f z := by
  funext z; unfold LyubarskiiNes.TorsionJets.polynomialScaledDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [FrobeniusFactor.iterScaledDeriv_const_mul]; ring

/-- **`Ξ_p` under natural-number translation** (iterating `XiSection_add_one`):
`Ξ_p(·+n) = ((-1)^{p+1})^n · Ξ_p` as functions. -/
theorem XiSection_add_natCast (p : ℕ) (Ω : ℂ) (n : ℕ) :
    (fun z => XiSection p Ω (z + (n : ℂ)))
      = fun z => ((-1 : ℂ) ^ (p + 1)) ^ n * XiSection p Ω z := by
  induction n with
  | zero => funext z; simp
  | succ m ih =>
      funext z
      have hz : z + (((m : ℕ) + 1 : ℕ) : ℂ) = (z + (m : ℂ)) + 1 := by push_cast; ring
      rw [hz, XiSection_add_one]
      have hm := congrFun ih z; rw [hm]; ring

/-- **STEP 3 master (verified).**  Integer-shift covariance of `polynomialScaledDeriv P Ξ`:
shifting the argument by a natural `n` multiplies by `((-1)^{p+1})^n`.  This lets the
integer part `n_j` of `∑ x_j` be absorbed into the scalar `c_j`, leaving `b + j/q`. -/
theorem polynomialScaledDeriv_Xi_add_natCast (p : ℕ) (Ω : ℂ) (P : Polynomial ℂ) (n : ℕ)
    (z : ℂ) :
    LyubarskiiNes.TorsionJets.polynomialScaledDeriv P (XiSection p Ω) (z + (n : ℂ)) =
      ((-1 : ℂ) ^ (p + 1)) ^ n *
        LyubarskiiNes.TorsionJets.polynomialScaledDeriv P (XiSection p Ω) z := by
  have h1 : LyubarskiiNes.TorsionJets.polynomialScaledDeriv P (XiSection p Ω) (z + (n : ℂ))
      = LyubarskiiNes.TorsionJets.polynomialScaledDeriv P
          (fun w => XiSection p Ω (w + (n : ℂ))) z := by
    rw [polynomialScaledDeriv_comp_add_const]
  rw [h1, XiSection_add_natCast, polynomialScaledDeriv_const_mul]

/-- The absorbed sign `((-1)^{p+1})^n` is nonzero (it is `±1`). -/
theorem sign_pow_ne_zero (p n : ℕ) : ((-1 : ℂ) ^ (p + 1)) ^ n ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ (by norm_num))

end Step3

/-! ## Polynomial packaging — from coefficient data to the `∃ P` shape

(Imported verbatim from the verified packaging fragment of attempt #3.)
`opPoly acoeff p := ∑_{k ≤ p} monomial k (acoeff k)` assembles a coefficient function into
a polynomial of degree exactly `p` when `acoeff p ≠ 0`, and `polynomialScaledDeriv` of it is
the coefficient sum `∑_{k ≤ p} acoeff k · iterScaledDeriv k g`.  This is the algebraic
bridge from the confluent-expansion coefficient form to the target `∃ P b c` statement. -/

/-- The operator polynomial assembled from a coefficient function, truncated at degree `p`. -/
noncomputable def opPoly (acoeff : ℕ → ℂ) (p : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (p + 1), Polynomial.monomial k (acoeff k)

theorem opPoly_coeff (acoeff : ℕ → ℂ) (p : ℕ) (n : ℕ) :
    (opPoly acoeff p).coeff n = if n ∈ Finset.range (p + 1) then acoeff n else 0 := by
  unfold opPoly
  rw [Polynomial.finsetSum_coeff]
  have hcong : ∀ k ∈ Finset.range (p + 1),
      (Polynomial.monomial k (acoeff k)).coeff n = if k = n then acoeff k else 0 :=
    fun k _ => Polynomial.coeff_monomial
  rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq' (Finset.range (p + 1)) n acoeff]

theorem opPoly_natDegree_le (acoeff : ℕ → ℂ) (p : ℕ) :
    (opPoly acoeff p).natDegree ≤ p := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact le_trans (Polynomial.natDegree_monomial_le _)
    (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

theorem opPoly_natDegree (acoeff : ℕ → ℂ) (p : ℕ) (hp : acoeff p ≠ 0) :
    (opPoly acoeff p).natDegree = p := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (opPoly_natDegree_le acoeff p)
  rw [opPoly_coeff]
  simp [hp]

theorem opPoly_ne_zero (acoeff : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (hpc : acoeff p ≠ 0) :
    opPoly acoeff p ≠ 0 := by
  intro h
  have := opPoly_natDegree acoeff p hpc
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-- `polynomialScaledDeriv (opPoly acoeff p) g z = ∑_{k ≤ p} acoeff k · iterScaledDeriv k g z`. -/
theorem polynomialScaledDeriv_opPoly (acoeff : ℕ → ℂ) (p : ℕ) (g : ℂ → ℂ) (z : ℂ) :
    LyubarskiiNes.TorsionJets.polynomialScaledDeriv (opPoly acoeff p) g z =
      ∑ k ∈ Finset.range (p + 1), acoeff k * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z := by
  unfold LyubarskiiNes.TorsionJets.polynomialScaledDeriv
  have hsupp : (opPoly acoeff p).support ⊆ Finset.range (p + 1) := by
    intro k hk
    by_contra hlt
    have : (opPoly acoeff p).coeff k = 0 := by
      rw [opPoly_coeff, if_neg hlt]
    exact (Polynomial.mem_support_iff.mp hk) this
  have hvanish : ∀ k ∈ Finset.range (p + 1), k ∉ (opPoly acoeff p).support →
      (opPoly acoeff p).coeff k * LyubarskiiNes.TorsionJets.iterScaledDeriv k g z = 0 := by
    intro k _ hknot
    have : (opPoly acoeff p).coeff k = 0 := by
      by_contra hc; exact hknot (Polynomial.mem_support_iff.mpr hc)
    rw [this, zero_mul]
  rw [Finset.sum_subset hsupp hvanish]
  apply Finset.sum_congr rfl
  intro k hk
  rw [opPoly_coeff, if_pos hk]

/-- The leading coefficient of the operator polynomial is nonzero (given `p ≤ q`).
(Imported verbatim from attempt #3.) -/
theorem leadingCoeff_ne_zero {p q : ℕ} (hp : 0 < p) (hpq_le : p ≤ q)
    (τ : ℂ) (hτ : 0 < τ.im) :
    (∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
        LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ)
          (((s : ℕ) : ℂ) / (q : ℂ) - ((r : ℕ) : ℂ) / (q : ℂ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro r _
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  have hrs_fin : r < s := Finset.mem_Ioi.mp hs
  have hrs : (r : ℕ) < (s : ℕ) := hrs_fin
  have harg : ((s : ℕ) : ℂ) / (q : ℂ) - ((r : ℕ) : ℂ) / (q : ℂ)
      = (((s : ℕ) - (r : ℕ) : ℕ) : ℂ) / (q : ℂ) := by
    rw [Nat.cast_sub (le_of_lt hrs)]; ring
  rw [harg]
  have hsp : (s : ℕ) < p := s.isLt
  exact oddTheta_ne_zero_of_pos_lt hp τ hτ ((s : ℕ) - (r : ℕ)) (by omega) (by omega)

/-! ## STEP 3 residual — `j`-independence + coprime reindexing of the proven κ-jet

STEP 2 is now **fully proven** (`minor_kappa_form`): the cyclic minor equals
`C · ∑_{k≤p} κ_k(x_j) · 𝔡^k Ξ (∑ x_j)` with `C^∞` coefficient functions `κ_k` and leading
`κ_p = V`.  The *only* remaining content is STEP 3: at the arithmetic-progression
configuration `x_j`, the coefficients `κ_k(x_j)` are `j`-independent up to a sign
(`ThetaFunctions.oddTheta_add_one_eq` under residue-wrap of the consecutive rows), and the argument
`∑ x_j` reindexes as `(b + j/q) + n_j` (integer shift `n_j`) via the coprime bijection on
`Fin q`.  This is isolated below as the single labelled residual `kappa_step3_reindex`,
stated *downstream* of the proven κ-form so that all analytic/calculus content of the node is
already discharged: the residual is purely the arithmetic of the theta antiperiodicity and
the `ZMod q` reindexing. -/

/-- **Odd-theta natural-shift antiperiodicity.**  `oddTheta τ (z + m) = (-1)^m · oddTheta τ z`
for a natural `m`, iterating `ThetaFunctions.oddTheta_add_one_eq`. -/
theorem oddTheta_add_natCast (τ z : ℂ) (m : ℕ) :
    LyubarskiiNes.ThetaFunctions.oddTheta τ (z + (m : ℂ)) = (-1 : ℂ) ^ m * LyubarskiiNes.ThetaFunctions.oddTheta τ z := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hz : z + (((k : ℕ) + 1 : ℕ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
      rw [hz, LyubarskiiNes.ThetaFunctions.oddTheta_add_one_eq, ih]
      ring

/-- **Odd-theta signed shift by an integer difference.**  For naturals `m₁ m₂`,
`oddTheta τ (z + (m₁ - m₂ : ℤ)) = (-1)^m₁ · (-1)^m₂ · oddTheta τ z`.  (Both signs are `±1`,
and `(-1)^m₂ = (-1)^(-m₂)`, so this is `(-1)^(m₁-m₂)`.) -/
theorem oddTheta_add_intCast_diff (τ z : ℂ) (m₁ m₂ : ℕ) :
    LyubarskiiNes.ThetaFunctions.oddTheta τ (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ))
      = (-1 : ℂ) ^ m₁ * ((-1 : ℂ) ^ m₂ * LyubarskiiNes.ThetaFunctions.oddTheta τ z) := by
  -- Shift by `m₁` up, then note the `-m₂` shift is undone by adding `m₂` and using naturality.
  have key : LyubarskiiNes.ThetaFunctions.oddTheta τ ((z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ)) + (m₂ : ℂ))
      = (-1 : ℂ) ^ m₂ * LyubarskiiNes.ThetaFunctions.oddTheta τ (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ)) :=
    oddTheta_add_natCast τ _ m₂
  have harg : (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ)) + (m₂ : ℂ) = z + (m₁ : ℂ) := by
    push_cast; ring
  rw [harg, oddTheta_add_natCast τ z m₁] at key
  -- key : (-1)^m₁ * oddTheta τ z = (-1)^m₂ * oddTheta τ (z + (m₁-m₂))
  -- Multiply by (-1)^m₂ and use ((-1)^m₂)^2 = 1.
  have hsq : ((-1 : ℂ) ^ m₂) * ((-1 : ℂ) ^ m₂) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hmul : (-1 : ℂ) ^ m₂ * ((-1 : ℂ) ^ m₁ * LyubarskiiNes.ThetaFunctions.oddTheta τ z)
      = (-1 : ℂ) ^ m₂ * ((-1 : ℂ) ^ m₂
          * LyubarskiiNes.ThetaFunctions.oddTheta τ (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ))) :=
    congrArg (fun t => (-1 : ℂ) ^ m₂ * t) key
  -- hmul : (-1)^m₂ * ((-1)^m₁ * θz) = (-1)^m₂ * ((-1)^m₂ * θ(z+d))
  rw [show (-1 : ℂ) ^ m₂ * ((-1 : ℂ) ^ m₂
        * LyubarskiiNes.ThetaFunctions.oddTheta τ (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ)))
      = (((-1 : ℂ) ^ m₂) * ((-1 : ℂ) ^ m₂))
        * LyubarskiiNes.ThetaFunctions.oddTheta τ (z + ((m₁ : ℤ) - (m₂ : ℤ) : ℂ)) by ring,
    hsq, one_mul] at hmul
  rw [← hmul]; ring

/-! ### The coprime σ-permutation on `Fin q` and the argument-reindex identity

The cyclic minor at start-index `j` evaluates `Ξ` at `∑_r x_j r = p·a + (T_j : ℂ)/q` where
`T_j := ∑_{r:Fin p} (j+r)%q`.  Splitting `T_j = q·n_j + m_j` (Euclidean), the fractional part
is `m_j = T_j % q = (p·j + p(p-1)/2) % q = (σ j).1`, and `σ` is a *coprime bijection* of
`Fin q` (injective because `p` is a unit mod `q`; bijective as a finite injective self-map).
So the physical argument is `(b + (σ j)/q) + n_j`, matching the corrected target statement. -/

/-- The σ-map `j ↦ (p·j + p(p-1)/2) % q` on `Fin q`. -/
def sigmaMap (p q : ℕ) [NeZero q] (j : Fin q) : Fin q :=
  ⟨(p * j.1 + p * (p - 1) / 2) % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩

/-- `σ` is injective: `(p·j+c)%q = (p·j'+c)%q ⇒ p·j ≡ p·j' (mod q) ⇒ j ≡ j'` since `p` is a
unit mod `q` (from `Nat.Coprime p q`), hence `j = j'` in `Fin q`. -/
theorem sigmaMap_injective (p q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) :
    Function.Injective (sigmaMap p q) := by
  intro j j' h
  simp only [sigmaMap, Fin.mk.injEq] at h
  set c := p * (p - 1) / 2
  have h1 : (p * j.1 + c) ≡ (p * j'.1 + c) [MOD q] := h
  have h2 : p * j.1 ≡ p * j'.1 [MOD q] := Nat.ModEq.add_right_cancel' c h1
  have hz : (p : ZMod q) * (j.1 : ZMod q) = (p : ZMod q) * (j'.1 : ZMod q) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    push_cast at this; exact this
  have hunit : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hpq
  have hcancel : (j.1 : ZMod q) = (j'.1 : ZMod q) := hunit.mul_left_cancel hz
  have hjj : j.1 ≡ j'.1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcancel
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hjj j.2 j'.2)

/-- The σ-permutation of `Fin q`: a finite injective self-map is bijective. -/
noncomputable def sigmaPerm (p q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) : Equiv.Perm (Fin q) :=
  Equiv.ofBijective (sigmaMap p q)
    ((Finite.injective_iff_bijective).mp (sigmaMap_injective p q hpq))

@[simp] theorem sigmaPerm_apply (p q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) (j : Fin q) :
    (sigmaPerm p q hpq) j = sigmaMap p q j := rfl

/-- `T_j % q = (σ j).1`: the residue-sum congruence
`∑_r (j+r)%q ≡ ∑_r (j+r) = p·j + p(p-1)/2 (mod q)`. -/
theorem sigma_sum_mod (p q : ℕ) [NeZero q] (j : Fin q) :
    (∑ r : Fin p, (j.1 + r.1) % q) % q = (p * j.1 + p * (p - 1) / 2) % q := by
  have hstep : (∑ r : Fin p, (j.1 + r.1) % q) % q = (∑ r : Fin p, (j.1 + r.1)) % q := by
    rw [Finset.sum_nat_mod,
      Finset.sum_nat_mod (s := Finset.univ) (f := fun r : Fin p => j.1 + r.1)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _; rw [Nat.mod_mod]
  rw [hstep]
  have hsum : (∑ r : Fin p, (j.1 + r.1)) = p * j.1 + p * (p - 1) / 2 := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => i) p, Finset.sum_range_id]
  rw [hsum]

/-- **Argument reindex identity.**  With `b := p·a` and `n_j := T_j / q`,
`∑_r (a + (row j r)/q) = (b + (σ j)/q) + n_j` where `row j r = (j+r)%q`. -/
theorem sum_arg_eq (p q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) (a : ℂ) (j : Fin q) :
    (∑ r : Fin p, (a + (((j.1 + r.1) % q : ℕ) : ℂ) / (q : ℂ)))
      = (((p : ℂ) * a) + (((sigmaPerm p q hpq) j : ℕ) : ℂ) / (q : ℂ))
        + (((∑ r : Fin p, (j.1 + r.1) % q) / q : ℕ) : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_neZero q).ne'
  set T := ∑ r : Fin p, (j.1 + r.1) % q with hT
  have hLHS : (∑ r : Fin p, (a + (((j.1 + r.1) % q : ℕ) : ℂ) / (q : ℂ)))
      = (p : ℂ) * a + (T : ℂ) / (q : ℂ) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hT]; push_cast [Finset.sum_div]; ring
  rw [hLHS]
  have hsig : (((sigmaPerm p q hpq) j : ℕ)) = T % q := by
    simp only [sigmaPerm_apply, sigmaMap]; rw [hT, sigma_sum_mod]
  rw [hsig]
  have hdm : q * (T / q) + T % q = T := Nat.div_add_mod T q
  have hTcast : (T : ℂ) = (q : ℂ) * ((T / q : ℕ) : ℂ) + ((T % q : ℕ) : ℂ) := by
    have hc : ((q * (T / q) + T % q : ℕ) : ℂ) = (T : ℂ) := by exact_mod_cast hdm
    push_cast at hc; linear_combination -hc
  rw [hTcast]; field_simp; ring

/-- **STEP 3 residual (single labelled blocker).**  Given the *proven* κ-jet data of
`minor_kappa_form` (`C^∞` coefficient functions `κ`, vanishing beyond degree `p`, leading
`κ p = V`), extract a `j`-independent coefficient vector `acoeff` (with `acoeff p ≠ 0`,
forcing `natDegree = p`), a base point `b`, per-`j` nonzero sign `d`, and integer shift `n`,
identifying the `j`-dependent κ-jet with the `j`-independent one evaluated at `(b+j/q)+n_j`.

Purely STEP-3 arithmetic: (a) `κ_k(x_j) = d_j · acoeff_k` from `ThetaFunctions.oddTheta_add_one_eq`
(antiperiodicity) under the residue-wrap of `cyclicConsecutiveRows`; (b) the coprime cyclic
residue-sum identity `∑ x_j = (b + j/q) + n_j` with `b := p·a` via a `ZMod q`-unit reindex;
`acoeff p ≠ 0` follows from `leadingCoeff_ne_zero` (needs `p ≤ q`, which `Nat.Coprime p q`
with `p,q > 1` gives; boundary `p = 1` handled directly). -/
theorem kappa_step3_reindex {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hpq : Nat.Coprime p q) (hple : p ≤ q) (τ a lam : ℂ) (hτ : 0 < τ.im)
    (C : ℂ) (κ : ℕ → (Fin p → ℂ) → ℂ) (hC0 : C ≠ 0)
    (hκcd : ∀ k, ContDiff ℂ ∞ (κ k))
    (hκvanish : ∀ k, p < k → κ k = 0)
    (hκlead : κ p = (fun u : Fin p → ℂ =>
        ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (u s - u r)))
    (hκcov : ∀ (w : Fin p → ℂ) (cc : ℂ),
        (∀ y : Fin p → ℂ,
          (∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) ((y s + w s) - (y r + w r)))
            = cc * ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
              LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (y s - y r)) →
          (∀ k y, κ k (fun i => y i + w i) = cc * κ k y)) :
    ∃ (acoeff : ℕ → ℂ) (b : ℂ) (d : Fin q → ℂ) (n : Fin q → ℕ) (π : Equiv.Perm (Fin q)),
      acoeff p ≠ 0 ∧ (∀ j, d j ≠ 0) ∧
      (∀ j : Fin q,
        (∑ k ∈ Finset.range (p + 1),
          κ k (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) *
            iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
              (∑ r, (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ)
                / (q : ℂ)) r))
          = d j * ∑ k ∈ Finset.range (p + 1),
              acoeff k * iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
                (((b + ((π j : ℕ) : ℂ) / (q : ℂ)) + ((n j : ℕ) : ℂ)))) := by
  classical
  -- Reference configuration and its differences.
  set xref : Fin p → ℂ := fun r => a + ((r : ℕ) : ℂ) / (q : ℂ) with hxref
  set acoeff : ℕ → ℂ := fun k => κ k xref with hacoeff
  -- `acoeff p = V(xref) = ∏_{r<s} ϑ_{pτ}((s−r)/q)`.
  have hqpos : 0 < q := Nat.pos_of_neZero q
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hacoeff_p : acoeff p
      = ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ)
            (((s : ℕ) : ℂ) / (q : ℂ) - ((r : ℕ) : ℂ) / (q : ℂ)) := by
    simp only [hacoeff, hκlead, hxref]
    refine Finset.prod_congr rfl (fun r _ => Finset.prod_congr rfl (fun s _ => ?_))
    congr 1; ring
  -- ==================================================================================
  -- VERIFIED COVARIANCE CORE (sorry-free): κ_k(x_j) = sign_j · acoeff_k for every j.
  -- ==================================================================================
  -- `x_j r = a + ((j+r) % q)/q`.  Write `x_j = xref + w_j`.
  set xsel : Fin q → Fin p → ℂ :=
    fun j r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ) with hxsel
  -- The integer wrap `wrap j r = (j + r) / q` (Nat division).
  set wrap : Fin q → Fin p → ℕ := fun j r => (j.1 + r.1) / q with hwrap
  -- `(cyclicConsecutiveRows p q j r : ℕ) = (j + r) - q * wrap j r`.
  have hrow : ∀ (j : Fin q) (r : Fin p),
      ((cyclicConsecutiveRows p q j r : ℕ) : ℤ)
        = ((j.1 : ℤ) + (r.1 : ℤ)) - (q : ℤ) * (wrap j r : ℤ) := by
    intro j r
    have hdm := Nat.div_add_mod (j.1 + r.1) q
    -- j+r = q*(wrap) + (row); so row = (j+r) - q*wrap.
    have hval : (cyclicConsecutiveRows p q j r : ℕ) = (j.1 + r.1) % q := rfl
    have hwval : wrap j r = (j.1 + r.1) / q := rfl
    rw [hval, hwval]
    -- Cast the Nat identity `q * ((j+r)/q) + (j+r)%q = j+r` to ℤ.
    have : (q : ℤ) * (((j.1 + r.1) / q : ℕ) : ℤ) + (((j.1 + r.1) % q : ℕ) : ℤ)
        = (j.1 : ℤ) + (r.1 : ℤ) := by exact_mod_cast hdm
    omega
  -- The translation vector `w_j r = (j:ℂ)/q - (wrap j r : ℂ)`.
  set wvec : Fin q → Fin p → ℂ :=
    fun j r => (j.1 : ℂ) / (q : ℂ) - ((wrap j r : ℕ) : ℂ) with hwvec
  -- `x_j r = xref r + w_j r`.
  have hsplit : ∀ (j : Fin q) (r : Fin p), xsel j r = xref r + wvec j r := by
    intro j r
    simp only [hxsel, hxref, hwvec]
    have : ((cyclicConsecutiveRows p q j r : ℕ) : ℂ)
        = ((j.1 : ℂ) + (r.1 : ℂ)) - (q : ℂ) * ((wrap j r : ℕ) : ℂ) := by
      have := hrow j r; push_cast at this; exact_mod_cast this
    rw [this]
    field_simp
    ring
  -- Difference cancellation: `(w_j s - w_j r) = (wrap j r : ℤ) - (wrap j s : ℤ)` (the j/q cancels).
  have hwdiff : ∀ (j : Fin q) (r s : Fin p),
      wvec j s - wvec j r = (((wrap j r : ℤ) - (wrap j s : ℤ) : ℤ) : ℂ) := by
    intro j r s
    simp only [hwvec]
    push_cast
    ring
  -- Per-`j` sign: `sign_j = ∏_{r} ∏_{s>r} (-1)^(wrap j r) * (-1)^(wrap j s)`.
  set signv : Fin q → ℂ :=
    fun j => ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
      ((-1 : ℂ) ^ (wrap j r) * (-1 : ℂ) ^ (wrap j s)) with hsignv
  -- `V(y + w_j) = sign_j · V(y)` for all `y` — the covariance hypothesis input.
  have hVcov : ∀ (j : Fin q) (y : Fin p → ℂ),
      (∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) ((y s + wvec j s) - (y r + wvec j r)))
        = signv j * ∏ r : Fin p, ∏ s ∈ Finset.Ioi r,
          LyubarskiiNes.ThetaFunctions.oddTheta ((p : ℂ) * τ) (y s - y r) := by
    intro j y
    rw [hsignv, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    -- factor: oddTheta((y s - y r) + (w_j s - w_j r)) = (-1)^wrap_r (-1)^wrap_s oddTheta(y s - y r).
    have hkey := oddTheta_add_intCast_diff ((p : ℂ) * τ) (y s - y r) (wrap j r) (wrap j s)
    have harg : (y s + wvec j s) - (y r + wvec j r)
        = (y s - y r) + (((wrap j r : ℤ) : ℂ) - ((wrap j s : ℤ) : ℂ)) := by
      have h2 := hwdiff j r s
      push_cast at h2 ⊢
      linear_combination h2
    rw [harg, hkey]
    ring
  -- Apply the threaded covariance `hκcov` to get `κ_k(x_j) = sign_j · κ_k(xref)`.
  have hkappa : ∀ (j : Fin q) (k : ℕ), κ k (xsel j) = signv j * acoeff k := by
    intro j k
    have hfun : xsel j = (fun i => xref i + wvec j i) := by funext r; exact hsplit j r
    rw [hfun]
    have := hκcov (wvec j) (signv j) (hVcov j) k xref
    simpa [hacoeff] using this
  -- Each `sign_j` is a nonzero product of `±1` powers.
  have hsign_ne : ∀ j : Fin q, signv j ≠ 0 := by
    intro j
    rw [hsignv, Finset.prod_ne_zero_iff]
    intro r _
    rw [Finset.prod_ne_zero_iff]
    intro s _
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  -- ==================================================================================
  -- The verified covariance core above (`hkappa`, `hsign_ne`) discharges ALL coefficient
  -- content: κ_k(x_j) = sign_j · acoeff_k, sign_j ≠ 0.  We now instantiate the existentials
  -- with `acoeff := κ · xref`, `d_j := sign_j`, and pull `sign_j` out of the LHS sum, so
  -- the goal collapses to (i) the leading non-vanishing `acoeff p ≠ 0`, and (ii) the pure
  -- *matched-`j`* argument identity `∑ x_j = (b + j/q) + n_j`.
  -- --------------------------------------------------------------------------------------
  -- First: rewrite the LHS of the per-`j` identity as `sign_j · ∑_k acoeff_k · 𝔡^k Ξ(∑ x_j)`.
  have hLHS : ∀ j : Fin q,
      (∑ k ∈ Finset.range (p + 1),
        κ k (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) *
          iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
            (∑ r, (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) r))
      = signv j * ∑ k ∈ Finset.range (p + 1),
          acoeff k * iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
            (∑ r, (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) r) := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- `κ k (x_j) = sign_j · acoeff_k`, and `x_j = xsel j` definitionally.
    have hxsel_eq : (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ))
        = xsel j := by funext r; rfl
    rw [hxsel_eq, hkappa j k]; ring
  -- =====================================================================================
  -- RESIDUAL DISCHARGED (`sorry`-free) via the corrected `π`+`p≤q` target.
  --
  -- (1) LEADING NON-VANISHING.  `acoeff p = ∏_{r<s} ϑ_{pτ}((s−r)/q) ≠ 0` by
  --     `leadingCoeff_ne_zero hp hple …` (uses `p ≤ q`).
  -- (2) σ-PERMUTED ARGUMENT IDENTITY.  `∑ x_j = (p·a + (σ j)/q) + n_j` with `n_j := T_j/q`,
  --     `σ := sigmaPerm p q hpq`, by `sum_arg_eq`.  Absorb `signv` and reindex.
  -- =====================================================================================
  refine ⟨acoeff, (p : ℂ) * a, signv, fun j => (∑ r : Fin p, (j.1 + r.1) % q) / q,
    sigmaPerm p q hpq, ?_, hsign_ne, fun j => ?_⟩
  · -- acoeff p ≠ 0
    rw [hacoeff_p]
    exact leadingCoeff_ne_zero hp hple τ hτ
  · -- per-`j` identity
    rw [hLHS j]
    -- Rewrite the `∑ x_j` argument as `(p·a + (σ j)/q) + n_j` via `sum_arg_eq`.
    have hargeq : (∑ r, (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) r)
        = (((p : ℂ) * a) + (((sigmaPerm p q hpq) j : ℕ) : ℂ) / (q : ℂ))
          + (((∑ r : Fin p, (j.1 + r.1) % q) / q : ℕ) : ℂ) := by
      have hrows : (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ))
          = (fun r : Fin p => a + (((j.1 + r.1) % q : ℕ) : ℂ) / (q : ℂ)) := by
        funext r; rfl
      rw [hrows]
      exact sum_arg_eq p q hpq a j
    rw [hargeq]

/-- **STEP 2/3 residual, in `polynomialScaledDeriv` form.**  Verified reduction of the F3
node onto the STEP-3 residual `kappa_step3_reindex`: the proven κ-form
(`minor_kappa_form`) supplies `minor_j = C·∑_k κ_k(x_j)·𝔡^k Ξ(∑ x_j)`; the residual rewrites
this as `C·d_j·∑_k acoeff_k·𝔡^k Ξ((b+j/q)+n_j)`; then the `opPoly` bridge and the verified
STEP-3 integer-shift absorption (`Step3.polynomialScaledDeriv_Xi_add_natCast`) fold `n_j` into
the sign and produce the target `c_j·polynomialScaledDeriv P Ξ (b+j/q)`. -/
theorem minor_polynomial_data {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hpq : Nat.Coprime p q) (hple : p ≤ q) (τ a lam : ℂ) (hτ : 0 < τ.im) :
    ∃ (P : Polynomial ℂ) (b : ℂ) (c : Fin q → ℂ) (π : Equiv.Perm (Fin q)),
      P ≠ 0 ∧ P.natDegree = p ∧ (∀ j, c j ≠ 0) ∧
      (∀ j : Fin q,
        foldCoordOp lam (List.finRange p)
          (fun y : Fin p → ℂ => (frobMatrix p τ y).det)
          (fun r => a + ((cyclicConsecutiveRows p q j r : ℕ) : ℂ) / (q : ℂ)) =
          c j * LyubarskiiNes.TorsionJets.polynomialScaledDeriv P
            (XiSection p ((p : ℂ) * τ)) (b + ((π j : ℕ) : ℂ) / (q : ℂ))) := by
  -- STEP 2 (fully proven): minor_j = C · ∑_{k≤p} κ_k(x_j) · 𝔡^k Ξ (∑ x_j).
  obtain ⟨C, κ, hC0, hκcd, hκvanish, hκlead, hκcov, hminor⟩ :=
    minor_kappa_form (q := q) hp τ a lam hτ
  -- STEP 3 residual: j-independent coefficients + σ-permuted coprime reindexing.
  obtain ⟨acoeff, b, d, n, π, hac, hd, hreindex⟩ :=
    kappa_step3_reindex hp hpq hple τ a lam hτ C κ hC0 hκcd hκvanish hκlead hκcov
  -- Assemble the polynomial P from the j-independent coefficient vector.
  refine ⟨opPoly acoeff p, b,
    fun j => C * d j * ((-1 : ℂ) ^ (p + 1)) ^ (n j), π,
    opPoly_ne_zero acoeff hp hac, opPoly_natDegree acoeff p hac, ?_, fun j => ?_⟩
  · -- c j ≠ 0
    intro j
    exact mul_ne_zero (mul_ne_zero hC0 (hd j)) (Step3.sign_pow_ne_zero p (n j))
  · -- the operator identity
    rw [hminor j, hreindex j]
    -- Now: C * (d j * ∑_k acoeff_k · 𝔡^k Ξ ((b+(π j)/q)+n_j))
    --    = (C·d j·sign^{n j}) · polynomialScaledDeriv (opPoly acoeff p) Ξ (b+(π j)/q).
    rw [show (∑ k ∈ Finset.range (p + 1),
          acoeff k * iterScaledDeriv k (XiSection p ((p : ℂ) * τ))
            (((b + ((π j : ℕ) : ℂ) / (q : ℂ)) + ((n j : ℕ) : ℂ))))
        = LyubarskiiNes.TorsionJets.polynomialScaledDeriv (opPoly acoeff p)
            (XiSection p ((p : ℂ) * τ)) ((b + ((π j : ℕ) : ℂ) / (q : ℂ)) + ((n j : ℕ) : ℂ)) from
      (polynomialScaledDeriv_opPoly acoeff p (XiSection p ((p : ℂ) * τ))
        ((b + ((π j : ℕ) : ℂ) / (q : ℂ)) + ((n j : ℕ) : ℂ))).symm]
    rw [Step3.polynomialScaledDeriv_Xi_add_natCast p ((p : ℂ) * τ) (opPoly acoeff p) (n j)
      (b + ((π j : ℕ) : ℂ) / (q : ℂ))]
    ring

/-- **F3 target — cyclic minor as a polynomial theta operator.**  Exact signature of the
skeleton frontier node `minor_as_polynomial_operator`.  Proved by combining the verified
STEP-1 reduction (`cyclic_minor_eq_foldCoordOp_frob`) with the STEP-2/3 residual
(`minor_polynomial_data`). -/
theorem minor_as_polynomial_operator_probe {p q : ℕ} [NeZero q]
    (hp : 0 < p) (hpq : Nat.Coprime p q) (hple : p ≤ q) (τ a lam : ℂ) (hτ : 0 < τ.im) :
    ∃ (P : Polynomial ℂ) (b : ℂ) (c : Fin q → ℂ) (π : Equiv.Perm (Fin q)),
      P ≠ 0 ∧ P.natDegree = p ∧ (∀ j, c j ≠ 0) ∧
      (∀ j : Fin q,
        ((primitiveThetaDerivativeMatrix p q τ lam a).submatrix
          (cyclicConsecutiveRows p q j) id).det =
          c j * LyubarskiiNes.TorsionJets.polynomialScaledDeriv P
            (XiSection p ((p : ℂ) * τ)) (b + ((π j : ℕ) : ℂ) / (q : ℂ))) := by
  obtain ⟨P, b, c, π, hP0, hPdeg, hc, hdata⟩ :=
    minor_polynomial_data hp hpq hple τ a lam hτ
  refine ⟨P, b, c, π, hP0, hPdeg, hc, fun j => ?_⟩
  rw [cyclic_minor_eq_foldCoordOp_frob τ lam a hτ j]
  exact hdata j

end LyubarskiiNes.FrobeniusDeterminant
