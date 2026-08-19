import LeanCode.Definitions

namespace LyubarskiiNes.ComplexAnalysis

open Filter
open scoped Topology

/-- Local division by a simple zero: if `E` has order exactly one at `z₀` and
`F` has order at least `k`, then `F / E ^ k` agrees on the punctured
neighborhood with an analytic function. -/
theorem local_div_pow_eventuallyEq
    {E F : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hE : AnalyticAt ℂ E z₀)
    (hF : AnalyticAt ℂ F z₀)
    (hEorder : analyticOrderAt E z₀ = (1 : ℕ∞))
    (hForder : (k : ℕ∞) ≤ analyticOrderAt F z₀) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧
      F / E ^ k =ᶠ[𝓝[≠] z₀] G := by
  rcases (AnalyticAt.analyticOrderAt_eq_natCast hE).1 hEorder with
    ⟨u, hu_an, hu_ne, hE_eq⟩
  rcases (natCast_le_analyticOrderAt hF).1 hForder with ⟨v, hv_an, hF_eq⟩
  refine ⟨fun z => v z / (u z) ^ k,
    hv_an.div (hu_an.pow k) (pow_ne_zero k hu_ne), ?_⟩
  filter_upwards [hE_eq.filter_mono nhdsWithin_le_nhds,
      hF_eq.filter_mono nhdsWithin_le_nhds,
      (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hEz hFz huz hz_ne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  change F z / E z ^ k = v z / (u z) ^ k
  calc
    F z / E z ^ k = ((z - z₀) ^ k * v z) / (((z - z₀) * u z) ^ k) := by
      simp [hEz, hFz, smul_eq_mul]
    _ = v z / (u z) ^ k := by
      rw [mul_pow]
      exact mul_div_mul_left (v z) ((u z) ^ k) (pow_ne_zero k hzsub)

/-- A zero of analytic order one is isolated. -/
theorem isolated_zero_of_analyticOrderAt_eq_one
    {E : ℂ → ℂ} {z₀ : ℂ}
    (hE : AnalyticAt ℂ E z₀)
    (hEorder : analyticOrderAt E z₀ = (1 : ℕ∞)) :
    ∀ᶠ z in 𝓝[≠] z₀, E z ≠ 0 := by
  rcases (AnalyticAt.analyticOrderAt_eq_natCast hE).1 hEorder with
    ⟨u, hu_an, hu_ne, hE_eq⟩
  filter_upwards [hE_eq.filter_mono nhdsWithin_le_nhds,
      (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hEz huz hz_ne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  rw [hEz]
  simp [smul_eq_mul, hzsub, huz]

/-- One-variable division by a simple divisor. If the zero set of `E` is `D`,
all its zeros have order one, and `F` has order at least `k` on `D`, then
`F / E ^ k` extends to an entire function. -/
theorem entire_div_pow_of_order_ge
    {D : Set ℂ} {E F : ℂ → ℂ} {k : ℕ}
    (hE : ∀ z, AnalyticAt ℂ E z)
    (hF : ∀ z, AnalyticAt ℂ F z)
    (hzero : ∀ z, E z = 0 ↔ z ∈ D)
    (hsimple : ∀ z ∈ D, analyticOrderAt E z = (1 : ℕ∞))
    (hForder : ∀ z ∈ D, (k : ℕ∞) ≤ analyticOrderAt F z) :
    ∃ Q : ℂ → ℂ, (∀ z, AnalyticAt ℂ Q z) ∧
      ∀ z, z ∉ D → Q z = F z / E z ^ k := by
  classical
  let q : ℂ → ℂ := F / E ^ k
  have hlocal : ∀ z, z ∈ D → ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ q =ᶠ[𝓝[≠] z] G := by
    intro z hz
    simpa [q] using local_div_pow_eventuallyEq (E := E) (F := F) (z₀ := z) (k := k)
      (hE z) (hF z) (hsimple z hz) (hForder z hz)
  let Q : ℂ → ℂ := fun z => if hz : z ∈ D then (Classical.choose (hlocal z hz)) z else q z
  refine ⟨Q, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ D
    · let G : ℂ → ℂ := Classical.choose (hlocal x hx)
      have hGspec : AnalyticAt ℂ G x ∧ q =ᶠ[𝓝[≠] x] G :=
        Classical.choose_spec (hlocal x hx)
      have hEnonzero : ∀ᶠ y in 𝓝[≠] x, E y ≠ 0 :=
        isolated_zero_of_analyticOrderAt_eq_one (E := E) (z₀ := x) (hE x) (hsimple x hx)
      have hnotD : ∀ᶠ y in 𝓝[≠] x, y ∉ D := by
        filter_upwards [hEnonzero] with y hEy hyD
        exact hEy ((hzero y).2 hyD)
      have hQG_punct : Q =ᶠ[𝓝[≠] x] G := by
        filter_upwards [hGspec.2, hnotD] with y hqy hyD
        simpa [Q, hyD] using hqy
      have hQG : Q =ᶠ[𝓝 x] G := by
        have hnear : ∀ᶠ y in 𝓝 x, y ∈ ({x}ᶜ : Set ℂ) → Q y = G y :=
          (eventually_nhdsWithin_iff).mp hQG_punct
        filter_upwards [hnear] with y hy
        by_cases hyx : y = x
        · subst y
          simp [Q, G, hx]
        · exact hy hyx
      exact hGspec.1.congr hQG.symm
    · have hEx : E x ≠ 0 := by
        intro hEx0
        exact hx ((hzero x).1 hEx0)
      have hEnonzero : ∀ᶠ y in 𝓝 x, E y ≠ 0 :=
        (hE x).continuousAt.eventually_ne hEx
      have hnotD : ∀ᶠ y in 𝓝 x, y ∉ D := by
        filter_upwards [hEnonzero] with y hEy hyD
        exact hEy ((hzero y).2 hyD)
      have hqQ : q =ᶠ[𝓝 x] Q := by
        filter_upwards [hnotD] with y hyD
        simp [Q, hyD]
      have hq_an : AnalyticAt ℂ q x := by
        simpa [q] using (hF x).div ((hE x).pow k) (pow_ne_zero k hEx)
      exact hq_an.congr hqQ
  · intro z hz
    simpa [q, Pi.div_apply, Pi.pow_apply] using (by simp [Q, hz] : Q z = q z)

end LyubarskiiNes.ComplexAnalysis
