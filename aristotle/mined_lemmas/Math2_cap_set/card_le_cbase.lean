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

lemma card_le_cbase (n : ℕ) (hn : 1 ≤ n) (A : Finset (Pt n))
    (hA : ThreeAPFree (A : Set (Pt n))) : (A.card : ℝ) ≤ 3 * cbase ^ n := by
  have h1 : (A.card : ℝ) ≤ ((3 * mcount n (2 * n / 3) : ℕ) : ℝ) := by
    exact_mod_cast card_le_three_mul_mcount n hn A hA
  exact h1.trans (three_mul_mcount_le_cbase n)

/-- The largest size of a 3AP-free subset of `𝔽₃ⁿ`. -/
