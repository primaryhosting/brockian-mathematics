/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The set of affine rational points of the plane Fermat curve
`F_n : x ^ n + y ^ n = 1` over `ℚ`.

For `n ≥ 4` this is a smooth plane curve of degree `n`, hence of genus
`(n-1)(n-2)/2 ≥ 3 ≥ 2`, so Faltings' theorem (the Mordell conjecture) predicts that it has
only finitely many rational points. -/

theorem fermatCurveRatPoints_four :
    fermatCurveRatPoints 4 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  apply Set.eq_of_subset_of_subset
  · rintro ⟨x, y⟩ hp
    have hmem := fermatCurveRatPoints_subset (n := 4) dvd_rfl (by norm_num) hp
    have hxy : x ^ 4 + y ^ 4 = 1 := hp
    obtain ⟨hx, hy⟩ := hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> subst hx <;> subst hy
    all_goals try norm_num at hxy
    all_goals norm_num
  · rintro ⟨x, y⟩ hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    show x ^ 4 + y ^ 4 = 1
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;> norm_num

end Frontier

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

