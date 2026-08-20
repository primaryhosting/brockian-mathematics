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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem ramseyProp_fourteen : RamseyProp 14 3 5 := by
  intro c hsymm
  by_cases h : ∃ S : Finset (Fin 14), S.card = 3 ∧ Mono c true S
  · exact Or.inl h
  · push_neg at h
    obtain ⟨S, -, hS5, hSm⟩ := exists_blue5 hsymm (fun S hS => h S hS) Finset.univ (by simp)
    exact Or.inr ⟨S, hS5, hSm⟩

/-! ### The extremal colouring on 13 vertices

The circulant graph `C₁₃(1,5)`: vertices `ZMod 13`, with `u` and `v` red-adjacent
iff `u - v ∈ {1, 5, 8, 12}`.  It has no red triangle and no blue set of size `5`. -/

/-- The difference `u - v` modulo `13`. -/
