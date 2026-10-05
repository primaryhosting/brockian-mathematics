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

theorem R_stabilises (hs : s < N) : R N adj s (N + 1) = R N adj s N := by
  by_cases hall : ∀ j < N, R N adj s (j + 1) ≠ R N adj s j
  · exfalso
    have h1 := R_card_ge (N := N) (adj := adj) (s := s) N hall
    have h2 : (R N adj s N).card ≤ N := by
      have := Finset.card_le_card (R_subset_range (adj := adj) hs N)
      simpa using this
    omega
  · push_neg at hall
    obtain ⟨j, hjN, hj⟩ := hall
    have hstab := R_stable_of_eq hj
    have e1 : R N adj s N = R N adj s j := by
      have := hstab (N - j); rwa [Nat.add_sub_cancel' (le_of_lt hjN)] at this
    have e2 : R N adj s (N + 1) = R N adj s j := by
      have := hstab (N + 1 - j); rwa [Nat.add_sub_cancel' (by omega : j ≤ N + 1)] at this
    rw [e1, e2]

