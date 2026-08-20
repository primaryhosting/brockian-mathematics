import Mathlib
namespace Brockian.MsFrobeniusGeneral

/-- Two-generator case: if `p` and `q` are coprime and `p > 0`, every `n ≥ p * q`
    is a nonnegative combination of `p` and `q`. -/

lemma exists_small_mul_add (g c m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime c g)
    (hm : c * g ≤ m) : ∃ z k : ℕ, z < g ∧ c * z + g * k = m := by
  obtain ⟨z, hz, hmod⟩ := exists_mod_solution g c m hg hcop
  refine ⟨z, (m - c * z) / g, hz, ?_⟩
  have hc : c * z ≤ m := by nlinarith
  have hdiv : g ∣ (m - c * z) := by
    have h1 : (m : ℤ) % g = (c * z : ℤ) % g := by
      norm_cast
      exact hmod.symm
    have h2 : (g : ℤ) ∣ ((m : ℤ) - (c * z : ℤ)) := Int.modEq_iff_dvd.mp h1.symm
    exact_mod_cast h2
  have heq : g * ((m - c * z) / g) = m - c * z := Nat.mul_div_cancel' hdiv
  omega

/-- The general Frobenius / numerical-semigroup theorem: for positive a,b,c with gcd(a,b,c)=1,
    every sufficiently large integer is a nonnegative combination a·x + b·y + c·z. -/
