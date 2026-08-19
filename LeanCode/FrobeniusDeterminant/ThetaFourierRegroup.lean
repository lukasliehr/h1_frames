import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Residue-class regrouping of a summable `ℤ`-series

The bridge from the abstract column de-Fourier reduction (`ColumnFourierReduction.lean`) to the
actual `primitiveThetaDerivativeMatrix`.  The matrix entry is `f(w + s/p)` for an entire `f`
given by an absolutely convergent `ℤ`-series `f(z) = ∑' n, gₜ(n, z)`; the `s/p` shift multiplies
the `n`-th term by `cexp(2πi·n·s/p) = ω^{n·s}` (`ω = exp(2πi/p)`), which depends only on `n mod p`.
Regrouping the summation index modulo `p` therefore turns the `s`-dependence into a finite Fourier
series `f(w + s/p) = ∑_{r : Fin p} c_r(w)·ω^{r·s}`.

The combinatorial heart of that regrouping — independent of `f` — is the lemma here:
`∑'_{n : ℤ} g n = ∑_{r : Fin p} ∑'_{k : ℤ} g (p·k + r)`,
the decomposition of a summable `ℤ`-series along the residue classes `mod p`.  It is fully
elementary (no analysis beyond `Summable`) and reusable.
-/

namespace LyubarskiiNes.FrobeniusDeterminant.Regroup

open scoped Topology Real

/-- The residue-class bijection `Fin p × ℤ ≃ ℤ`, `(r, k) ↦ p·k + r`.  For `p > 0` every integer
has a unique representation as `p·k + r` with `0 ≤ r < p`. -/
noncomputable def residueEquiv (p : ℕ) (hp : 0 < p) : Fin p × ℤ ≃ ℤ :=
  Equiv.ofBijective (fun x : Fin p × ℤ => (p : ℤ) * x.2 + (x.1 : ℕ)) (by
    constructor
    · rintro ⟨⟨r, hr⟩, k⟩ ⟨⟨r', hr'⟩, k'⟩ h
      have hd : (p : ℤ) ∣ ((r' : ℤ) - r) := ⟨k - k', by linear_combination -h⟩
      have h1 : (r : ℤ) % (p : ℤ) = (r' : ℤ) % (p : ℤ) := Int.modEq_iff_dvd.mpr hd
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr),
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr')] at h1
      have hreq : r = r' := by exact_mod_cast h1
      subst hreq
      have hk : (p : ℤ) * k = (p : ℤ) * k' := by linarith
      have : k = k' := mul_left_cancel₀ (by exact_mod_cast hp.ne') hk
      subst this
      rfl
    · intro n
      refine ⟨(⟨(n % p).toNat, ?_⟩, n / p), ?_⟩
      · have hlt : n % (p : ℤ) < p := Int.emod_lt_of_pos n (by exact_mod_cast hp)
        have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg n (by exact_mod_cast hp.ne')
        omega
      · have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg n (by exact_mod_cast hp.ne')
        show (p : ℤ) * (n / p) + ((n % p).toNat : ℤ) = n
        rw [Int.toNat_of_nonneg h0]
        exact Int.mul_ediv_add_emod n p)

@[simp] lemma residueEquiv_apply (p : ℕ) (hp : 0 < p) (r : Fin p) (k : ℤ) :
    residueEquiv p hp (r, k) = (p : ℤ) * k + (r : ℕ) := rfl

/-- **Residue-class regrouping of a summable `ℤ`-series.**  A summable family over `ℤ` may be
summed by first fixing the residue `r mod p` and summing over the arithmetic progression
`{p·k + r : k ∈ ℤ}`, then summing the `p` residues.  This is the index-side combinatorics behind
expanding `jacobiTheta₂ (w + s/p)` into a finite Fourier series in `s`. -/
theorem tsum_int_regroup_mod {p : ℕ} (hp : 0 < p) {g : ℤ → ℂ} (hg : Summable g) :
    ∑' n : ℤ, g n = ∑ r : Fin p, ∑' k : ℤ, g ((p : ℤ) * k + (r : ℕ)) := by
  have hF : Summable (fun x : Fin p × ℤ => g (residueEquiv p hp x)) :=
    (residueEquiv p hp).summable_iff.mpr hg
  have hfib : ∀ r : Fin p, Summable (fun k : ℤ => g (residueEquiv p hp (r, k))) := by
    intro r
    have hinj : Function.Injective (fun k : ℤ => residueEquiv p hp (r, k)) := by
      intro a b hab
      simp only [residueEquiv_apply] at hab
      have : (p : ℤ) * a = (p : ℤ) * b := by linarith
      exact mul_left_cancel₀ (by exact_mod_cast hp.ne') this
    exact hg.comp_injective hinj
  rw [← (residueEquiv p hp).tsum_eq g, hF.tsum_prod' hfib, tsum_fintype]
  simp only [residueEquiv_apply]

open Complex

/-- Shifting the theta argument by `s/p` multiplies the `n`-th term by the phase
`cexp(2πi·n·s/p)`. -/
lemma jacobiTheta₂_term_add_div (p : ℕ) (n : ℤ) (w τ : ℂ) (s : Fin p) :
    jacobiTheta₂_term n (w + (s : ℕ) / (p : ℂ)) τ
      = jacobiTheta₂_term n w τ * Complex.exp (2 * π * I * n * ((s : ℕ) / (p : ℂ))) := by
  unfold jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The phase of the `(p·k + r)`-th term at shift `s/p` collapses to `ω^{r·s}`
(`ω = exp(2πi/p)`): the `p·k` part contributes `cexp(2πi·k·s) = 1`. -/
lemma phase_collapse {p : ℕ} (hp : 0 < p) (k : ℤ) (r s : Fin p) :
    Complex.exp (2 * π * I * (((p : ℤ) * k + (r : ℕ) : ℤ) : ℂ) * ((s : ℕ) / (p : ℂ)))
      = Complex.exp (2 * π * I / p) ^ ((r : ℕ) * (s : ℕ)) := by
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsplit : 2 * π * I * (((p : ℤ) * k + (r : ℕ) : ℤ) : ℂ) * ((s : ℕ) / (p : ℂ))
      = ((k * (s : ℤ) : ℤ) : ℂ) * (2 * π * I)
        + (((r : ℕ) * (s : ℕ) : ℕ) : ℂ) * (2 * π * I / p) := by
    field_simp
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_nat_mul]

/-- **The theta function folds into a finite Fourier series under a `s/p` shift.**
`jacobiTheta₂ (w + s/p) τ = ∑_{r : Fin p} c_r(w) · ω^{r·s}`, where `ω = exp(2πi/p)` and the
coefficient `c_r(w) = ∑'_{k} jacobiTheta₂_term (p·k + r) w τ` is the residue-`r` partial theta
series.  This is the concrete column de-Fourier factorization for the actual `jacobiTheta₂`:
together with `ColumnFourierReduction`, it exhibits the theta sample matrix as `D · V` with `V`
the (nonsingular) DFT matrix and `D` the coefficient matrix `c_r(a + t/q)`. -/
theorem jacobiTheta₂_add_div_fourier {p : ℕ} (hp : 0 < p) (w τ : ℂ) (hτ : 0 < τ.im) (s : Fin p) :
    jacobiTheta₂ (w + (s : ℕ) / (p : ℂ)) τ
      = ∑ r : Fin p, (∑' k : ℤ, jacobiTheta₂_term ((p : ℤ) * k + (r : ℕ)) w τ)
          * Complex.exp (2 * π * I / p) ^ ((r : ℕ) * (s : ℕ)) := by
  have hsum : Summable (fun n : ℤ => jacobiTheta₂_term n (w + (s : ℕ) / (p : ℂ)) τ) :=
    (summable_jacobiTheta₂_term_iff _ τ).mpr hτ
  rw [jacobiTheta₂, tsum_int_regroup_mod hp hsum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← tsum_mul_right]
  refine tsum_congr (fun k => ?_)
  rw [jacobiTheta₂_term_add_div p ((p : ℤ) * k + (r : ℕ)) w τ s, phase_collapse hp k r s]

/-- The derivative term satisfies the same phase law: `jacobiTheta₂'_term = 2πi·n · jacobiTheta₂_term`
multiplies the same phase. -/
lemma jacobiTheta₂'_term_add_div (p : ℕ) (n : ℤ) (w τ : ℂ) (s : Fin p) :
    jacobiTheta₂'_term n (w + (s : ℕ) / (p : ℂ)) τ
      = jacobiTheta₂'_term n w τ * Complex.exp (2 * π * I * n * ((s : ℕ) / (p : ℂ))) := by
  unfold jacobiTheta₂'_term
  rw [jacobiTheta₂_term_add_div p n w τ s]
  ring

/-- **The `z`-derivative of theta also folds into a finite Fourier series under a `s/p` shift**,
with the same DFT structure (coefficients are the residue-`r` partial `jacobiTheta₂'` series). -/
theorem jacobiTheta₂'_add_div_fourier {p : ℕ} (hp : 0 < p) (w τ : ℂ) (hτ : 0 < τ.im) (s : Fin p) :
    jacobiTheta₂' (w + (s : ℕ) / (p : ℂ)) τ
      = ∑ r : Fin p, (∑' k : ℤ, jacobiTheta₂'_term ((p : ℤ) * k + (r : ℕ)) w τ)
          * Complex.exp (2 * π * I / p) ^ ((r : ℕ) * (s : ℕ)) := by
  have hsum : Summable (fun n : ℤ => jacobiTheta₂'_term n (w + (s : ℕ) / (p : ℂ)) τ) :=
    (summable_jacobiTheta₂'_term_iff _ τ).mpr hτ
  rw [jacobiTheta₂', tsum_int_regroup_mod hp hsum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← tsum_mul_right]
  refine tsum_congr (fun k => ?_)
  rw [jacobiTheta₂'_term_add_div p ((p : ℤ) * k + (r : ℕ)) w τ s, phase_collapse hp k r s]

end LyubarskiiNes.FrobeniusDeterminant.Regroup
