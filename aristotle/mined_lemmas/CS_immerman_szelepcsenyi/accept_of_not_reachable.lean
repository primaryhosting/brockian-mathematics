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

theorem accept_of_not_reachable (hs : s < N) {t : ℕ} (ht : t < N)
    (h : ¬ Relation.ReflTransGen (Edge N adj) s t) :
    Relation.ReflTransGen (Step N adj s t) start .acc := by
  have htR : t ∉ R N adj s N := fun hmem => h (reachable_of_mem_R hs N t hmem)
  have hN : 1 ≤ N := by omega
  have hround := reach_round (adj := adj) hs (t := t) N hN (le_refl _)
  have houter := reach_outer hs (t := t) (i := N) (c := ((R N adj s (N - 1)).card))
    hN (le_refl _) rfl N (le_refl _)
  have hreach1 := hround.trans houter
  rw [filter_lt_N_eq hs] at hreach1
  have hlast : Step N adj s t
      (.outer N ((R N adj s (N-1)).card) N ((R N adj s N).card))
      (.inner (N + 1) ((R N adj s N).card) t 0 0 0) := Step.lastRound
  have hcheck : ∀ w ∈ R N adj s (N + 1 - 1), w ≠ t ∧ adj w t = false := by
    intro w hw
    rw [show N + 1 - 1 = N by omega] at hw
    constructor
    · rintro rfl; exact htR hw
    · by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have : t ∈ R N adj s (N + 1) := mem_R_succ_of_edge hw ht hcon
      rw [R_stabilises hs] at this
      exact htR this
  obtain ⟨lb', hinner⟩ := reach_inner hs (t := t) (i := N + 1)
    (c := ((R N adj s N).card)) (v := t) (k := 0)
    (by rw [show N + 1 - 1 = N by omega]) hcheck
    ((R N adj s N).card) 0 0 (by rw [show N + 1 - 1 = N by omega]; simp) (by omega)
  have hacc : Step N adj s t (.inner (N + 1) ((R N adj s N).card) t 0 ((R N adj s N).card) lb')
      .acc := Step.accept rfl
  exact (((hreach1.tail hlast).trans hinner).tail hacc)

/-- The complement machine accepts exactly when `t` is unreachable from `s`. -/
