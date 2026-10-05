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

lemma sum_half_pow_edeg (n : ℕ) :
    ∑ α : Exp n, (1 / 2 : ℝ) ^ (edeg α) = (7 / 4) ^ n := by
  have h3 : (∑ b : Fin 3, (1 / 2 : ℝ) ^ (b : ℕ)) = 7 / 4 := by
    simp [Fin.sum_univ_three]; norm_num
  have h : ((7 : ℝ) / 4) ^ n = ∏ _i : Fin n, ∑ b : Fin 3, (1 / 2 : ℝ) ^ (b : ℕ) := by
    rw [Finset.prod_const, h3, Finset.card_univ, Fintype.card_fin]
  rw [h, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [edeg, ← Finset.prod_pow_eq_pow_sum]

/-- A Chernoff-type bound on the number of low degree monomials. -/
