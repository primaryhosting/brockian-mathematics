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

lemma capSetMax_div_cube_le (n : ℕ) :
    ((capSetMax n : ℝ) / 3 ^ n) ^ 3 ≤ 27 * (1372 / 1728 : ℝ) ^ n := by
  have hnat := capSetMax_pow_le n
  have hR : ((capSetMax n : ℝ)) ^ 3 * 64 ^ n ≤ 27 * 1372 ^ n := by exact_mod_cast hnat
  have h27 : ((3 : ℝ) ^ n) ^ 3 = 27 ^ n := by
    rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
  have hsplit : (1372 / 1728 : ℝ) ^ n = 1372 ^ n / (64 ^ n * 27 ^ n) := by
    rw [div_pow, ← mul_pow]; norm_num
  rw [div_pow, h27, div_le_iff₀ (by positivity), hsplit]
  have h64 : (0 : ℝ) < 64 ^ n := by positivity
  rw [show (27 : ℝ) * (1372 ^ n / (64 ^ n * 27 ^ n)) * 27 ^ n
      = 27 * 1372 ^ n / 64 ^ n by field_simp, le_div_iff₀ h64]
  exact hR

/-- The density of a maximal cap set in `𝔽₃ⁿ` tends to `0`. -/
