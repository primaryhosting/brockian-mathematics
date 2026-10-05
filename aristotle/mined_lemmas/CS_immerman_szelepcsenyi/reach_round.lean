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

theorem reach_round (hs : s < N) {t : ℕ} :
    ∀ i, 1 ≤ i → i ≤ N → Relation.ReflTransGen (Step N adj s t)
      start (.outer i ((R N adj s (i - 1)).card) 0 0) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
      intro _ hiN
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simp only [start, Nat.add_sub_cancel, R_zero, Finset.card_singleton]
        exact .refl
      · have hprev := ih hipos (by omega)
        have houter := reach_outer hs (t := t) (i := i) (c := ((R N adj s (i - 1)).card))
          hipos (by omega) rfl N (le_refl _)
        have hlast : Step N adj s t
            (.outer i ((R N adj s (i-1)).card) N ((R N adj s i).card))
            (.outer (i + 1) ((R N adj s i).card) 0 0) := Step.nextRound (by omega)
        have := (hprev.trans houter)
        rw [filter_lt_N_eq hs] at this
        simpa using this.tail hlast

/-- **Completeness**: if `t` is not reachable from `s`, the complement machine accepts. -/
