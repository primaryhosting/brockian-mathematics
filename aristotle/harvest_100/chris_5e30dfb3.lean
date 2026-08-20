/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as a plain block comment, and is repeated as the
-- module docstring immediately after the imports.)

import Mathlib

/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- **Baire category theorem.**  A nonempty complete metric space is not the union of
countably many nowhere dense sets: if `X` is a complete metric space which is
nonempty, and `s : ℕ → Set X` is a sequence of nowhere dense subsets
(`interior (closure (s n)) = ∅`), then their union is not all of `X`.

The key Mathlib ingredient is `nonempty_interior_of_iUnion_of_closed`, the Baire
category theorem for `BaireSpace`s (complete metric spaces are `BaireSpace`s via
the instance `BaireSpace.of_pseudoEMetricSpace_completeSpace`). -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (s : ℕ → Set X) (hs : ∀ n, IsNowhereDense (s n)) :
    (⋃ n, s n) ≠ Set.univ := by
  intro hunion
  -- Replace each `s n` by its closure: still nowhere dense, and still covering `X`.
  have hcov : (⋃ n, closure (s n)) = Set.univ := by
    refine Set.eq_univ_of_subset ?_ hunion
    exact Set.iUnion_mono fun n => subset_closure
  obtain ⟨n, hn⟩ :=
    nonempty_interior_of_iUnion_of_closed (fun n => isClosed_closure) hcov
  rw [hs n] at hn
  exact hn.ne_empty rfl

end Math

