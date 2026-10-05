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

lemma Arrow.mono {s s' : Finset V} {k : ℕ} (h : Arrow G s k) (hs : s ⊆ s') : Arrow G s' k := by
  rcases h with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · exact Or.inl ⟨t, ht.trans hs, h⟩
  · exact Or.inr ⟨t, ht.trans hs, h⟩

section Deg

variable [DecidableRel G.Adj]

/-- The neighbours of `v` inside `s`. -/
