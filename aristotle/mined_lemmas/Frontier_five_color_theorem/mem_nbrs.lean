import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

lemma mem_nbrs {s : Finset V} {G : SimpleGraph V} {v x : V} :
    x ∈ nbrs s G v ↔ (x ∈ s ∧ x ≠ v ∧ G.Adj v x) := by
  simp [nbrs, Finset.mem_filter, Finset.mem_erase, and_assoc]
  tauto

