import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

namespace Frontier

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

lemma chain_pos {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ y ∈ chain n c t, 0 < y := by
  induction t with
  | zero => simp [chain]
  | succ t ih =>
      intro y hy
      rw [chain, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact (next_spec n c _).1
      · exact ih y hy

/-- The main homogeneity computation: every small subset of a stage of the chain gets the
"limit colour" of the empty set. -/
