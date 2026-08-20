import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem insert_mem_V (hlim : IsSuccLimit o) (hx : x ∈ V_ o) (hy : y ∈ V_ o) :
    insert x y ∈ V_ o := by
  refine mem_V_of_rank_lt ?_
  rw [rank_insert]
  exact max_lt (hlim.succ_lt (rank_lt_of_mem_V hx)) (rank_lt_of_mem_V hy)

