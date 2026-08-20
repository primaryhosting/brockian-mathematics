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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real ComplexConjugate InnerProductSpace
open Complex MeasureTheory Submodule AddCircle Module

namespace Brockian.Weyl.DeficiencyODE

/-! ## Abstract setting: symmetric operators, deficiency vectors, essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

/-- A densely defined operator `T` with domain `D` is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

lemma spanBasis_induction {b : HilbertBasis ι ℂ H}
    {P : (span ℂ (Set.range (b : ι → H))) → Prop}
    (mem : ∀ i, P (spanBasis b i)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : ℂ) x, P x → P (c • x)) (x : span ℂ (Set.range (b : ι → H))) : P x := by
  have hx : x ∈ span ℂ (Set.range (spanBasis b)) := by
    rw [(spanBasis b).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact mem i
  | zero => exact zero
  | add x y _ _ hx hy => exact add _ _ hx hy
  | smul c x _ hx => exact smul _ _ hx

/-- The diagonal (unbounded) operator with eigenvalues `lam i` and eigenvectors `b i`, defined on
the algebraic span of the Hilbert basis `b`. -/
