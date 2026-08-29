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

/-- The number of elements of `A` below `n`. -/

theorem szemerediStatement_of_finitary {k : ℕ} (h : FinitarySzemeredi k) :
    SzemerediStatement k := by
  rintro A ⟨δ, hδ, hden⟩
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  obtain ⟨n, hn, hcard⟩ := hden N₀
  obtain ⟨a, d, hd, hmem⟩ :=
    hN₀ n hn ((Finset.range n).filter (fun x => x ∈ A)) (Finset.filter_subset _ _)
      (by simpa [countIn] using hcard)
  exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.1 (hmem i hi)).2⟩

/-- The statement of Szemerédi's theorem holds for all lengths `k ≤ 3`. -/
