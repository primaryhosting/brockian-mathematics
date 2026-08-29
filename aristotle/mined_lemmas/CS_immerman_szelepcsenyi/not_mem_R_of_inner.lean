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

theorem not_mem_R_of_inner {i c v k d lb : ℕ} (h : Inv N adj s t (.inner i c v k d lb))
    (hd : d = c) : v ∉ R N adj s i := by
  obtain ⟨hi1, -, hc, -, -, -, S, hS, hScard, hSprop⟩ := h
  have hSsub : S ⊆ R N adj s (i - 1) := hS.trans (Finset.filter_subset _ _)
  have hcard : (R N adj s (i - 1)).card ≤ S.card := by omega
  have hSeq : S = R N adj s (i - 1) := Finset.eq_of_subset_of_card_le hSsub hcard
  intro hv
  have hi : i - 1 + 1 = i := by omega
  rw [← hi, mem_R_succ_iff] at hv
  rcases hv with hv | ⟨-, u, hu, huv⟩
  · exact ((hSprop v (hSeq ▸ hv)).1) rfl
  · exact absurd (hSprop u (hSeq ▸ hu)).2 (by simp [huv])

