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

theorem reach_pathB {t i c v k d u : ℕ} :
    ∀ l, l ≤ i - 1 → ∀ p ∈ R N adj s l, ∃ l' ≤ l,
      Relation.ReflTransGen (Step N adj s t) (.pathB i c v k d u s 0) (.pathB i c v k d u p l') := by
  intro l
  induction l with
  | zero =>
      intro _ p hp
      simp only [R_zero, Finset.mem_singleton] at hp
      subst hp
      exact ⟨0, le_refl _, .refl⟩
  | succ l ih =>
      intro hl p hp
      rw [mem_R_succ_iff] at hp
      rcases hp with hp | ⟨hpN, u', hu, hadj⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) p hp
        exact ⟨l', by omega, hreach⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) u' hu
        exact ⟨l' + 1, by omega, hreach.tail (Step.stepB hadj hpN (by omega))⟩

/-- The inner loop can enumerate all of `R (i-1)`, provided every element of `R (i-1)`
passes the two checks. -/
