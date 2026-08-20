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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem accessibleInfo_le_holevoChi [Nonempty Y] [DecidableEq Y]
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) (hρ1 : ∀ x, (ρ x).trace = 1) :
    accessibleInfo Y p ρ ≤ holevoChi p ρ := by
  have hne : Nonempty {E : Y → Mat n // IsPOVM E} := by
    classical
    refine ⟨⟨fun y => if y = Classical.arbitrary Y then 1 else 0, ?_, ?_⟩⟩
    · intro y
      by_cases h : y = Classical.arbitrary Y <;>
        simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
    · simp
  exact ciSup_le fun E => holevo_bound hp0 hp1 hρ hρ1 E.2

end QI

import Mathlib

/-!
# Basic definitions for quantum information

We work with finite dimensional quantum systems, whose states are density matrices in
`Matrix (Fin n) (Fin n) ℂ`.
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

/-- Square complex matrices of size `n`, the operators on an `n`-dimensional quantum system. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ}

/-- The matrix logarithm, defined through the continuous functional calculus.  For a positive
definite matrix `A` with spectral decomposition `A = U * diagonal μ * Uᴴ` we have
`logM A = U * diagonal (Real.log ∘ μ) * Uᴴ`. -/
