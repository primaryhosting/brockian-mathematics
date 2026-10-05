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
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem immerman_szelepcsenyi_space {C : Type*} [Fintype C] (step : C → C → Bool) (a b : C) :
    ∃ F : Finset IS.Cfg, F.card ≤ 5 * (Fintype.card C + 2) ^ 8 ∧
      ∀ x : IS.Cfg, Relation.ReflTransGen
        (IS.Step (Fintype.card C) (adjOf step) (enc C a : ℕ) (enc C b : ℕ)) IS.start x → x ∈ F :=
  ⟨IS.cfgBound (Fintype.card C), IS.card_cfgBound_le _,
    fun _ hx => IS.reachable_mem_cfgBound (enc C a).isLt (enc C b).isLt hx⟩

end CS

