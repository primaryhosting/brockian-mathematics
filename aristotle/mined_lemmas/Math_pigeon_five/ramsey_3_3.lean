/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pigeonhole for five two-valued items: among five booleans, some three of them
(at three distinct positions) are equal. -/

theorem ramsey_3_3 :
    (∀ col : Fin 6 → Fin 6 → Bool, (∀ i j, col i j = col j i) →
      ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        col x y = col x z ∧ col x y = col y z) ∧
    (∃ col : Fin 5 → Fin 5 → Bool, (∀ i j, col i j = col j i) ∧
      ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
        ¬ (col x y = col x z ∧ col x y = col y z)) := by
  refine ⟨fun col _ => ?_, ⟨pent, pent_symm, pent_no_mono_triangle⟩⟩
  rcases pigeon_five (col 0 1) (col 0 2) (col 0 3) (col 0 4) (col 0 5) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mono_triangle_of_three_same col 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 2 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 2 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 3 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2

end Math

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

