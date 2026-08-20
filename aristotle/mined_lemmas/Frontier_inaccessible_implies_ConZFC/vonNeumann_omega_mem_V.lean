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

theorem vonNeumann_omega_mem_V (h : ω < o) : V_ (ω : Ordinal.{u}) ∈ V_ o :=
  mem_V_of_rank_lt (by rw [rank_vonNeumann]; exact h)

end VonNeumann

/-! ## Cardinal arithmetic at an inaccessible cardinal -/

section Inaccessible

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal, the beth function stays below it. -/
