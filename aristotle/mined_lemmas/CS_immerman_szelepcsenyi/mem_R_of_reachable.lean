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

theorem mem_R_of_reachable (hs : s < N) {x : ℕ}
    (h : Relation.ReflTransGen (Edge N adj) s x) : x ∈ R N adj s N := by
  have key : ∀ y, Relation.ReflTransGen (Edge N adj) s y → ∃ i, y ∈ R N adj s i := by
    intro y hy
    induction hy with
    | refl => exact ⟨0, by simp [R_zero]⟩
    | tail hab hbc ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, mem_R_succ_of_edge hi hbc.2.1 hbc.2.2⟩
  obtain ⟨i, hi⟩ := key x h
  rcases Nat.lt_or_ge i N with h' | h'
  · exact R_mono (le_of_lt h') hi
  · rwa [R_eq_of_ge hs h'] at hi

