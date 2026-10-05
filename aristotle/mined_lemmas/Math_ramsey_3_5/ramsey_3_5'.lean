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

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

/-! ## Basic notions: cliques and independent sets relative to a finite vertex set -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `IsCl G t` says that the finite set `t` is a clique of `G`. -/

theorem ramsey_3_5' :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ t : Finset (Fin n), G.IsNClique 3 t) ∨
      (∃ t : Finset (Fin n), G.IsNIndepSet 5 t)} 14 := by
  obtain ⟨hmem, hlb⟩ := ramsey_3_5
  constructor
  · intro G
    rcases hmem G with ⟨t, htc, hti⟩ | ⟨t, htc, hti⟩
    · exact Or.inl ⟨t, isCl_iff.mp hti, htc⟩
    · exact Or.inr ⟨t, isInd_iff.mp hti, htc⟩
  · intro n hn
    refine hlb (fun G => ?_)
    rcases hn G with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, ht.2, isCl_iff.mpr ht.1⟩
    · exact Or.inr ⟨t, ht.2, isInd_iff.mpr ht.1⟩

end Math

