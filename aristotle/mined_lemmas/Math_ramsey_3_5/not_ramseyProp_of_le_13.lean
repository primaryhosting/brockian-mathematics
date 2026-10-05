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

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

theorem not_ramseyProp_of_le_13 {n : ℕ} (hn : n ≤ 13) : ¬ RamseyProp n 3 5 := by
  intro hR
  set f : Fin n → Fin 13 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    simp only [hf, Fin.mk.injEq] at hxy
    exact Fin.ext hxy
  rcases hR (H.comap f) with ⟨S, hS⟩ | ⟨S, hS⟩
  · exact H_triangle_free _ (isNClique_image f hfinj H hS)
  · refine H_no_indep_five (S.image f) (isNClique_image f hfinj Hᶜ ?_)
    refine hS.mono ?_
    intro x y hxy
    exact ⟨fun h => hxy.1 (hfinj h), hxy.2⟩

/-- **R(3,5) = 14**. -/
