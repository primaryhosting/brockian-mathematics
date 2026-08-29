/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/

lemma insert_inter_insert (a : α) (s t : Finset α) :
    insert a s ∩ insert a t = insert a (s ∩ t) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  tauto

/-- Auxiliary form of the Erdős–Rado sunflower lemma: a `w`-uniform family with more than
`w ! * k ^ w` members contains a sunflower with `k + 1` petals. -/
