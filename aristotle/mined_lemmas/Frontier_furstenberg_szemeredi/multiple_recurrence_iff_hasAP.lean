/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

theorem multiple_recurrence_iff_hasAP (A : Set ℕ) (k : ℕ) :
    (∃ d : ℕ, 0 < d ∧ (⋂ i ∈ Finset.range k, (fun n => n + i * d) ⁻¹' A).Nonempty) ↔
      HasAP A k := by
  constructor
  · rintro ⟨d, hd, a, ha⟩
    refine ⟨a, d, hd, fun i hi => ?_⟩
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage] at ha
    exact ha i hi
  · rintro ⟨a, d, hd, h⟩
    refine ⟨d, hd, a, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage]
    exact fun i hi => h i hi

end

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

