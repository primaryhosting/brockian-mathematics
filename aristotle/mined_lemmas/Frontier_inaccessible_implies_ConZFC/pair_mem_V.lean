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

theorem pair_mem_V (hlim : IsSuccLimit o) (hx : x ∈ V_ o) (hy : y ∈ V_ o) :
    ({x, y} : ZFSet.{u}) ∈ V_ o :=
  insert_mem_V hlim hx (insert_mem_V hlim hy (empty_mem_V hlim.bot_lt))

