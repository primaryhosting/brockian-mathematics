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

lemma card_Nb_add_card_Mb {s : Finset V} {v : V} (hv : v ∈ s) :
    (Nb G s v).card + (Mb G s v).card = s.card - 1 := by
  have h1 : Nb G s v = (s.erase v).filter (fun u => G.Adj v u) := by
    unfold Nb
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hadj⟩
      exact ⟨⟨fun h => G.irrefl (h ▸ hadj), hu⟩, hadj⟩
    · rintro ⟨⟨_, hu⟩, hadj⟩
      exact ⟨hu, hadj⟩
  rw [h1]
  unfold Mb
  rw [Finset.card_filter_add_card_filter_not (p := fun u => G.Adj v u),
    Finset.card_erase_of_mem hv]

/-- If `v` has at least `k` neighbours in `s` and there is no triangle in `s`, then
there is an independent set of size `k` inside `s`. -/
