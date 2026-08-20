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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/

theorem landauCountUnbounded_iff :
    LandauCountUnbounded ↔ {p : ℕ | IsLandauPrime p}.Infinite := by
  refine ⟨LandauFourthConjecture, fun h B => ?_⟩
  -- The set of arguments is infinite, hence contains more than `B` elements below some `x`.
  have hA : LandauArguments.Infinite := by
    intro hfin
    refine h ?_
    have : {p : ℕ | IsLandauPrime p} ⊆ (fun n : ℕ => n ^ 2 + 1) '' LandauArguments := by
      rintro p ⟨hp, n, rfl⟩
      exact ⟨n, hp, rfl⟩
    exact Set.Finite.subset (hfin.image _) this
  obtain ⟨s, hs, hcard⟩ := hA.exists_subset_card_eq (B + 1)
  obtain ⟨x, hx⟩ := s.exists_le
  have hsub : s ⊆ (Finset.range (x + 1)).filter (fun n => Nat.Prime (n ^ 2 + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hx n hn; omega, hs hn⟩
  have hle : B + 1 ≤ landauCount x := by
    rw [landauCount, ← hcard]
    exact Finset.card_le_card hsub
  exact ⟨x, hle⟩

/-! ## Reduction from the Hardy–Littlewood lower bound -/

/-- The Hardy–Littlewood (Bateman–Horn) prediction for `n ^ 2 + 1` in a weakened, purely
lower-bound form: for some constant `c > 0` one has `landauCount x ≥ c * x / log x`
for all large `x`. -/
