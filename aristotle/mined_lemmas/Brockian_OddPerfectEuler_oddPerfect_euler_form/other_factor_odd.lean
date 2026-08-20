/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma other_factor_odd {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (h : (∏ x ∈ s, f x) % 4 = 2)
    {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfx : f x % 2 = 0) (hxy : y ≠ x) :
    f y % 2 = 1 := by
  -- If f y were even, combined with f x being even, the product would be 0 mod 4
  by_contra hfynotodd
  have hfyeven : f y % 2 = 0 := by omega
  -- The product f x * f y divides the total product, and is divisible by 4
  have hdiv : 4 ∣ (∏ z ∈ s, f z) := by
    have hprodxy : f x * f y ∣ ∏ z ∈ s, f z := by
      have hsub : {x, y} ⊆ s := by
        intro z hz
        simp at hz
        rcases hz with rfl | rfl <;> assumption
      rw [← Finset.prod_pair hxy.symm]
      exact Finset.prod_dvd_prod_of_subset (s := {x, y}) (t := s) (f := f) hsub
    have h4divxy : 4 ∣ f x * f y := by
      have : 2 ∣ f x := Nat.dvd_of_mod_eq_zero hfx
      have : 2 ∣ f y := Nat.dvd_of_mod_eq_zero hfyeven
      obtain ⟨a, ha⟩ := this
      have : 2 ∣ f x := Nat.dvd_of_mod_eq_zero hfx
      obtain ⟨b, hb⟩ := this
      use a * b
      rw [hb, ha]
      ring
    exact Nat.dvd_trans h4divxy hprodxy
  omega

