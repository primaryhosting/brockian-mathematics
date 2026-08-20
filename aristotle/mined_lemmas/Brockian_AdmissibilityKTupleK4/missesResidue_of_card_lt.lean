import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A `k`-tuple of integers `h : Fin k → ℤ` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the values
`h 0, …, h (k-1)` do not cover every residue class modulo `p`. -/

theorem missesResidue_of_card_lt {k : ℕ} (h : Fin k → ℤ) (p : ℕ) [Fact p.Prime]
    (hp : k < p) : ∃ r : ZMod p, ∀ i, (h i : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsurj : Function.Surjective (fun i : Fin k => ((h i : ZMod p))) := by
    intro r
    obtain ⟨i, hi⟩ := hcon r
    exact ⟨i, hi⟩
  have := Fintype.card_le_of_surjective _ hsurj
  simp [ZMod.card] at this
  omega

/-- **Admissibility criterion for 4-tuples.** A 4-tuple of integers is admissible
if and only if it fails to cover all residue classes modulo `2` and modulo `3`;
no other prime needs to be checked. -/
