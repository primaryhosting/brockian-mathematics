import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma betrothed_subset_union : Betrothed ⊆ BetrothedSmall ∪ BetrothedLarge := by
  rintro n ⟨m, hm⟩
  rcases lt_trichotomy m n with h | h | h
  · exact Or.inr ⟨m, hm, h⟩
  · exact absurd h hm.2.2.1
  · exact Or.inl ⟨m, hm, h⟩

/-- Pairing each larger member with its (smaller) partner is injective, so the
larger members are at most as numerous as the smaller members. -/
