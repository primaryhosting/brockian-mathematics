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

theorem not_ramseyProp_of_le {N : ℕ} (hN : N ≤ 13) : ¬ RamseyProp N 3 5 := by
  intro hR
  set f : Fin N ↪ Fin 13 := ⟨Fin.castLE hN, Fin.castLE_injective hN⟩ with hf
  have hsymm : ∀ u v : Fin N, col13 (f u) (f v) = col13 (f v) (f u) :=
    fun u v => col13_symm _ _
  rcases hR (fun u v => col13 (f u) (f v)) hsymm with ⟨S, hS3, hSm⟩ | ⟨S, hS5, hSm⟩
  · exact col13_no_red3 (S.map f) (by rw [Finset.card_map, hS3]) (mono_map col13 f true S hSm)
  · exact col13_no_blue5 (S.map f) (by rw [Finset.card_map, hS5]) (mono_map col13 f false S hSm)

/-- **The Ramsey number `R(3,5)` equals `14`.** -/
