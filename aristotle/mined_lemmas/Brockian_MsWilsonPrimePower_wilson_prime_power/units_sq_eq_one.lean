import Mathlib
namespace Brockian.MsWilsonPrimePower

open Finset

/-- If an odd prime power `p ^ k` divides `(a - 1) * (a + 1)`, then it divides one of the two
factors, since `p` cannot divide both `a - 1` and `a + 1`. -/

private lemma units_sq_eq_one (p k : ℕ) (hp : p.Prime) (hodd : Odd p)
    (x : (ZMod (p ^ k))ˣ) (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set y : ZMod (p ^ k) := (x : ZMod (p ^ k)) with hy
  have hy2 : y * y = 1 := by
    simpa using congrArg (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k))) hx
  set a : ℤ := (y.val : ℤ) with ha
  have hya : ((a : ℤ) : ZMod (p ^ k)) = y := by simp [ha]
  have hprod : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ k)) = 0 := by
    push_cast
    rw [hya]
    linear_combination hy2
  have hdvd : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp hprod
    push_cast at h
    exact h
  rcases prime_pow_dvd_of_dvd_pred_mul_succ p k hp hodd a hdvd with h1 | h1
  · left
    have h2 : ((a - 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h1
    push_cast at h2
    rw [hya] at h2
    have h3 : y = 1 := by linear_combination h2
    exact Units.ext (by simpa [hy] using h3)
  · right
    have h2 : ((a + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h1
    push_cast at h2
    rw [hya] at h2
    have h3 : y = -1 := by linear_combination h2
    exact Units.ext (by simpa [hy] using h3)

/-- The product of all units of `ZMod (p ^ k)`, taken in the unit group, is `-1`.

The product of all elements of a finite abelian group equals the product of its self-inverse
elements; here those are exactly `1` and `-1`. -/
