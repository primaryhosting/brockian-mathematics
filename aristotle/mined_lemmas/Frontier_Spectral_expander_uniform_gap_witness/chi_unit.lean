import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem chi_unit {k : ℕ} (S : Finset (Fin k)) (i : Fin k) :
    chi S (unit i) = if i ∈ S then -1 else 1 := by
  unfold chi
  by_cases hi : i ∈ S
  · rw [if_pos hi, ← Finset.prod_erase_mul _ _ hi, unit_apply_self, eps_one,
      Finset.prod_eq_one (fun j hj => ?_), one_mul]
    rw [unit_apply_ne (Finset.ne_of_mem_erase hj), eps_zero]
  · rw [if_neg hi]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [unit_apply_ne (by rintro rfl; exact hi hj), eps_zero]

