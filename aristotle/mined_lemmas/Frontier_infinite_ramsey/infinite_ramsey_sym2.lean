import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set


theorem infinite_ramsey_sym2 (c : Sym2 ℕ → Fin 2) :
    ∃ (S : Set ℕ) (i : Fin 2), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = i := by
  obtain ⟨S, i, hS, hmono⟩ := infinite_ramsey fun x y => c s(x, y)
  refine ⟨S, i, hS, fun x hx y hy hxy => ?_⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact hmono x hx y hy h
  · rw [Sym2.eq_swap]
    exact hmono y hy x hx h

end Frontier

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

