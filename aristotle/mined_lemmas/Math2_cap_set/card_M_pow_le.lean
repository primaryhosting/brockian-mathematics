/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

lemma card_M_pow_le (n : ℕ) : ((M n (2 * n / 3)).card) ^ 3 * 64 ^ n ≤ 1372 ^ n := by
  have h := card_M_bound n (2 * n / 3)
  set m : ℕ := (M n (2 * n / 3)).card with hm
  have hpos : (0 : ℚ) < ((1 : ℚ) / 2) ^ (2 * n / 3) := by positivity
  have h2 : (m : ℚ) ≤ 2 ^ (2 * n / 3) * (7 / 4) ^ n := by
    rw [← le_div_iff₀ hpos] at h
    have hkey : ((1 : ℚ) / 2) ^ (2 * n / 3) = 1 / 2 ^ (2 * n / 3) := by rw [div_pow, one_pow]
    have hkey2 : (7 / 4 : ℚ) ^ n / (1 / (2 : ℚ) ^ (2 * n / 3))
        = (7 / 4 : ℚ) ^ n * 2 ^ (2 * n / 3) := by field_simp
    rw [hkey, hkey2] at h
    calc (m : ℚ) ≤ (7 / 4) ^ n * 2 ^ (2 * n / 3) := h
      _ = 2 ^ (2 * n / 3) * (7 / 4) ^ n := by ring
  have h3 : (m : ℚ) ^ 3 ≤ (2 ^ (2 * n / 3)) ^ 3 * ((7 / 4) ^ n) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 3
  have h4 : ((2 : ℚ) ^ (2 * n / 3)) ^ 3 ≤ 4 ^ n := by
    rw [← pow_mul]
    calc (2 : ℚ) ^ (2 * n / 3 * 3) ≤ 2 ^ (2 * n) := by
          apply pow_le_pow_right₀ (by norm_num); omega
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  have h5 : (m : ℚ) ^ 3 * 64 ^ n ≤ 1372 ^ n := by
    have h6 : ((7 / 4 : ℚ) ^ n) ^ 3 = (343 / 64 : ℚ) ^ n := by
      rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
    calc (m : ℚ) ^ 3 * 64 ^ n ≤ ((2 ^ (2 * n / 3)) ^ 3 * ((7 / 4) ^ n) ^ 3) * 64 ^ n :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (4 ^ n * (343 / 64 : ℚ) ^ n) * 64 ^ n := by
          rw [h6]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h4 (by positivity)) (by positivity)
      _ = 1372 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
  have hfin : (((m ^ 3 * 64 ^ n : ℕ)) : ℚ) ≤ ((1372 ^ n : ℕ) : ℚ) := by push_cast; exact h5
  exact_mod_cast hfin

end Counting

section Asymptotic

open Filter

/-- The maximal size of a subset of `𝔽₃ⁿ` containing no three-term arithmetic progression
(a *cap set*). -/
