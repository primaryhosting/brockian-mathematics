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
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/

lemma phaseEq_trans {u v w : Qubit} (h₁ : PhaseEq u v) (h₂ : PhaseEq v w) : PhaseEq u w := by
  obtain ⟨z, hz, ha, hb⟩ := h₁
  obtain ⟨y, hy, ha', hb'⟩ := h₂
  exact ⟨y * z, by simp [hy, hz], by rw [ha', ha, mul_assoc], by rw [hb', hb, mul_assoc]⟩

instance qubitSetoid : Setoid Qubit where
  r := PhaseEq
  iseqv := ⟨phaseEq_refl, phaseEq_symm, phaseEq_trans⟩

/-- Pure qubit states modulo global phase. -/
