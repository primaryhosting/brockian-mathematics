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

lemma KK_ne_zero_deg {n : ℕ} {α β γ : Exp n} (h : KK α β γ ≠ 0) :
    edeg β + edeg γ = edeg α := by
  have hall : ∀ i, kk (α i) (β i) (γ i) ≠ 0 := fun i hi =>
    h (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hcoord : ∀ i, (β i : ℕ) + (γ i : ℕ) = (α i : ℕ) := by
    intro i
    by_contra hc
    exact hall i (by simp [kk, hc])
  simp only [edeg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hcoord i

