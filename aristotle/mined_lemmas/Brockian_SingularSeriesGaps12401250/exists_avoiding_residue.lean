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

/-- A finite set of integers is *admissible* (in the sense of the prime `k`-tuples
conjecture) if for every prime `p` it fails to cover all residue classes modulo `p`. -/

lemma exists_avoiding_residue (p : ℕ) [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) (x : ZMod p) :
    ∃ r : ZMod p, r ≠ 0 ∧ r ≠ x := by
  have hcard : ({(0 : ZMod p), x} : Finset (ZMod p)).card < Fintype.card (ZMod p) := by
    have h1 : ({(0 : ZMod p), x} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  obtain ⟨r, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (by simpa using hcard : _ < (Finset.univ : Finset (ZMod p)).card)
  exact ⟨r, by simp at hr; tauto, by simp at hr; tauto⟩

/-- The pair `{0, h}` is admissible exactly when the gap `h` is even. -/
