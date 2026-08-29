/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

namespace CS

/-- A finite constraint satisfaction problem (CSP) instance: `numVars` variables taking
values in an alphabet of size `alphabetSize`, together with a nonempty list of Boolean
constraints on assignments. -/
structure CSP where
  numVars : ℕ
  alphabetSize : ℕ
  alphabet_pos : 0 < alphabetSize
  constraints : List ((Fin numVars → Fin alphabetSize) → Bool)
  constraints_ne : constraints ≠ []

namespace CSP

/-- Assignments of the CSP `G`. -/

theorem size_iterate_le {C : ℕ} (hsize : ∀ G : CSP, (amp G).size ≤ C * G.size)
    (G : CSP) (t : ℕ) : (amp^[t] G).size ≤ C ^ t * G.size := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc (amp (amp^[n] G)).size ≤ C * (amp^[n] G).size := hsize _
      _ ≤ C * (C ^ n * G.size) := Nat.mul_le_mul_left _ ih
      _ = C ^ (n + 1) * G.size := by ring

/-- Completeness is preserved along the iteration. -/
