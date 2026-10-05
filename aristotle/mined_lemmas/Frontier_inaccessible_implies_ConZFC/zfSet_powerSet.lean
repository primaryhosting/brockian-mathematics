import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The first-order language of set theory

We build the first-order language with a single binary relation symbol `∈`, write down a
standard axiomatization of `ZFC` in it (extensionality, empty set, pairing, union, power set,
infinity, foundation, choice, together with the separation and replacement schemes), and prove
that Mathlib's type `ZFSet` of ZFC-sets is a model of this theory.
-/

namespace Frontier

open FirstOrder Language

universe u

/-- The relation symbols of the language of set theory: a single binary relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory. -/

theorem zfSet_powerSet : ZFSet.{u} ⊨ powerSetAx := by
  have key : ∀ x : ZFSet.{u}, ∃ p, ∀ w, w ∈ p ↔ ∀ z, z ∈ w → z ∈ x :=
    fun x => ⟨x.powerset, fun _ => by
      rw [ZFSet.mem_powerset]; exact ⟨fun h _ hz => h hz, fun h _ hz => h _ hz⟩⟩
  simpa [powerSetAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

