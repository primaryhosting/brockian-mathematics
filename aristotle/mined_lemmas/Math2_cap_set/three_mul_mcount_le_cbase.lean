import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma three_mul_mcount_le_cbase (n : ℕ) :
    ((3 * mcount n (2 * n / 3) : ℕ) : ℝ) ≤ 3 * cbase ^ n := by
  have h := mcount_le n (2 * n / 3)
  have hpos : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ n := by positivity
  have h2 : (2 : ℝ) ^ (2 * n / 3) * (7 / 4) ^ n ≤ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ n * (7 / 4) ^ n :=
    mul_le_mul_of_nonneg_right (pow_two_le n) hpos
  have hc : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ n * (7 / 4) ^ n = cbase ^ n := by
    rw [cbase, mul_pow]
  push_cast
  nlinarith [h, h2, hc]

/-- The exponential form of the cap set bound. -/
