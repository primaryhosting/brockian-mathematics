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

/-- `A` contains an arithmetic progression of length `k`, i.e. there are `a` and a positive
common difference `d` with `a, a + d, …, a + (k-1) * d` all in `A`. -/

lemma hasAPOfLength_three_of_average {A : Set ℕ} {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxyz : x + z = y + y) (hne : x ≠ y) : HasAPOfLength A 3 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨x, y - x, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hx
    · have h1 : x + 1 * (y - x) = y := by omega
      rw [h1]; exact hy
    · have h2 : x + 2 * (y - x) = z := by omega
      rw [h2]; exact hz
  · refine ⟨z, y - z, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hz
    · have h1 : z + 1 * (y - z) = y := by omega
      rw [h1]; exact hy
    · have h2 : z + 2 * (y - z) = x := by omega
      rw [h2]; exact hx

/-- Sanity check: the hypothesis `UpperDensityPos` is satisfiable (`Set.univ` has density `1`). -/
