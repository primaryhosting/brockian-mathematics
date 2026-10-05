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

theorem card_cfgBound_le (N : ℕ) : (cfgBound N).card ≤ 5 * (N + 2) ^ 8 := by
  have h4 : (N + 2) ^ 4 ≤ (N + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : (N + 2) ^ 6 ≤ (N + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (N + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have e1 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2)).image
      fun q => Cfg.outer q.1 q.2.1 q.2.2.1 q.2.2.2).card ≤ (N+2)^4 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e2 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.pathA q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).card ≤ (N+2)^6 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e3 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.inner q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).card ≤ (N+2)^6 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e4 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2)).image
      fun q => Cfg.pathB q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1
        q.2.2.2.2.2.2.2).card ≤ (N+2)^8 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e5 : ({Cfg.acc} : Finset Cfg).card = 1 := rfl
  unfold cfgBound
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) ?_
  rw [e5]
  omega

