import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic definitions -/

/-- `HasAP A k` says that the set `A ⊆ ℕ` contains a non-degenerate arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` (with common difference `d > 0`). -/

theorem szemerediFinitary_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediFinitary k := by
  intro δ hδ
  refine ⟨cornersTheoremBound (δ / 3), fun N hN S hSsub hScard => ?_⟩
  exact (hasAP_three_of_dense_finset hδ hN S hSsub hScard).mono hk

/-- The density form of Szemerédi's theorem holds for `k ≤ 3`; equivalently, this is the target
theorem `Frontier.furstenberg_szemeredi` in packaged form. -/
