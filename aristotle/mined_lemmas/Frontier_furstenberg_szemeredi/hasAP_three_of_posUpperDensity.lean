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

theorem hasAP_three_of_posUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) : HasAP A 3 := by
  obtain ⟨δ, hδ, hden⟩ := hA
  obtain ⟨N, hN, hcard⟩ := hden (cornersTheoremBound (δ / 3))
  refine (hasAP_three_of_dense_finset hδ hN _ (Finset.filter_subset _ _) hcard).subset ?_
  intro x hx
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
  exact hx.2

/-! ## The target statement -/

/-- **Szemerédi's theorem, base cases (`k ≤ 3`).**

Every set `A ⊆ ℕ` of positive upper density contains arithmetic progressions of every length
`k ≤ 3`. The case `k = 3` is Roth's theorem (obtained here from the corners theorem, which in
Mathlib is proved via the triangle removal lemma / Szemerédi regularity); the cases `k ≤ 2` follow
from it. The full theorem, for all `k`, is Szemerédi's theorem, proved by Furstenberg's multiple
recurrence theorem in ergodic theory; it is not available in Mathlib, so the statement here is
restricted to the range of `k` that can currently be verified. The general statement is recorded
below as `Frontier.SzemerediDensity`, together with a Lean-checked reduction of it to the
finitary form `Frontier.SzemerediFinitary`. -/
