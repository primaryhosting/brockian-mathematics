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

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

theorem ramsey_3_5 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique 3 s) ∨
        (∃ t : Finset (Fin N), Gᶜ.IsNClique 5 t)} 14 := by
  constructor
  · intro G
    rcases Ramsey35.ramsey_3_5_finset G Finset.univ (by simp) with ⟨s, _, hs⟩ | ⟨t, _, ht⟩
    · exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨t, ht⟩
  · intro N hN
    by_contra hlt
    push_neg at hlt
    have h13 : (13 : ℕ) ∈ Ramsey35.RamseySet :=
      Ramsey35.RamseySet_upward (by omega) hN
    rcases h13 Ramsey35.G13 with h | h
    · exact Ramsey35.G13_triangle_free h
    · exact Ramsey35.G13_no_indep_five h

end Math

