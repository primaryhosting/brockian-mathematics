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

lemma capSetMax_pow_le (n : ℕ) : (capSetMax n) ^ 3 * 64 ^ n ≤ 27 * 1372 ^ n := by
  have h1 := capSetMax_le n
  have h2 := card_M_pow_le n
  calc (capSetMax n) ^ 3 * 64 ^ n ≤ (3 * (M n (2 * n / 3)).card) ^ 3 * 64 ^ n :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 3)
    _ = 27 * (((M n (2 * n / 3)).card) ^ 3 * 64 ^ n) := by ring
    _ ≤ 27 * 1372 ^ n := Nat.mul_le_mul_left _ h2

