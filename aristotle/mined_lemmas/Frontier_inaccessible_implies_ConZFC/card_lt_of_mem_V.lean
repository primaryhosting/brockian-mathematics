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

theorem card_lt_of_mem_V (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord) :
    ZFSet.card x < κ := by
  have h1 : ZFSet.card x ≤ ZFSet.card (V_ (rank x)) := ZFSet.card_mono (subset_vonNeumann_self x)
  rw [card_vonNeumann] at h1
  exact lt_of_le_of_lt h1 (preBeth_lt_of_lt_ord hκ (rank_lt_of_mem_V hx))

/-- `V_ κ.ord` is closed under images of families indexed by one of its elements: this is the
key use of inaccessibility (regularity plus the strong limit property). -/
