import Mathlib

/-!
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Infinity

/-- The naturals are countably infinite: `Nat` is a `Countable` type and is `Infinite`. -/
theorem nat_countable : Countable Nat ∧ Infinite Nat := by
  constructor
  · -- `Nat` is countable: the identity is an injection into `Nat`.
    exact ⟨⟨id, Function.injective_id⟩⟩
  · -- `Nat` is infinite: otherwise `Nat ≃ Fin n`, and the first `n + 1` naturals
    -- would inject into `Fin n`, contradicting a cardinality count.
    refine ⟨fun hfin => ?_⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Nat
    have hinj : Function.Injective (fun i : Fin (n + 1) => e (i : Nat)) := by
      intro i j hij
      have : (i : Nat) = (j : Nat) := e.injective hij
      exact Fin.ext this
    have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card (Fin n) :=
      Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcard
    omega

end Infinity

