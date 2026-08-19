import Mathlib.Analysis.Fourier.ZMod
import LeanCode.Definitions

namespace LyubarskiiNes.TorsionJets

/-- Orthogonality of the standard additive character on `ZMod q`.

This is the finite character-sum step used in the Fourier-to-residue identity.
The later theta-series statement still needs the Part 3 residue series `B_ell`
as an actual Lean object. -/
theorem zmod_stdAddChar_sum_mul_eq_ite {q : ℕ} [NeZero q] (t : ZMod q) :
    (∑ j : ZMod q, ZMod.stdAddChar (t * j)) = if t = 0 then (q : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht]
    have hvanish : (∑ j : ZMod q, (ZMod.stdAddChar.mulShift t) j) = (0 : ℂ) :=
      AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar q) ht)
    simpa [AddChar.mulShift_apply] using hvanish

/-- Averaged integer-frequency form of finite character orthogonality.

This is the root-of-unity selector used in the Part 7 gamma-fiber row change:
after averaging over one period, exactly the integer frequencies divisible by
`q` survive. -/
theorem zmod_stdAddChar_average_int_eq_ite {q : ℕ} [NeZero q] (n : ℤ) :
    ((q : ℂ)⁻¹) *
        (∑ j : ZMod q, ZMod.stdAddChar ((n : ZMod q) * j)) =
      if (q : ℤ) ∣ n then 1 else 0 := by
  have hsum := zmod_stdAddChar_sum_mul_eq_ite (q := q) (t := (n : ZMod q))
  by_cases hdiv : (q : ℤ) ∣ n
  · have hz : (n : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n q).2 hdiv
    have hqC : (q : ℂ) ≠ 0 := by
      exact_mod_cast (NeZero.ne q)
    rw [if_pos hdiv, hsum, if_pos hz]
    exact inv_mul_cancel₀ hqC
  · have hz : (n : ZMod q) ≠ 0 := by
      intro hz
      exact hdiv ((ZMod.intCast_zmod_eq_zero_iff_dvd n q).1 hz)
    rw [if_neg hdiv, hsum, if_neg hz]
    simp

end LyubarskiiNes.TorsionJets
