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
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

For a CHSH tuple `A₀, A₁, B₀, B₁` (four self-adjoint involutions, with the `Aᵢ` commuting with
the `Bⱼ`) inside a unital C*-algebra, the CHSH operator

  `M = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies Tsirelson's bound `‖M‖ ≤ 2 √2`.

The proof is the classical one: one checks the algebraic identity

  `M ^ 2 = 4 - [A₀, A₁] * [B₀, B₁]`,

each commutator has norm at most `2` (since each entry is a self-adjoint involution, hence of
norm one), so `‖M ^ 2‖ ≤ 8`; since `M` is self-adjoint, the C*-identity gives
`‖M‖ ^ 2 = ‖M ^ 2‖ ≤ 8`, i.e. `‖M‖ ≤ 2 √2`.

The statement is given for an arbitrary unital C*-algebra; since the algebra `H →L[ℂ] H` of
bounded operators on a Hilbert space is such an algebra, the usual statement about the operator
norm of the quantum CHSH operator follows (see `QC.chsh_tsirelson_operator`).
-/

namespace QC

open scoped Real

variable {R : Type*}

/-- The CHSH operator associated with four observables. -/

theorem chshOp_sq {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ ^ 2 = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  obtain ⟨hA0, hA1, hB0, hB1, -, -, -, -, c00, c01, c10, c11⟩ := T
  simp only [pow_two] at hA0 hA1 hB0 hB1
  have d00 : ∀ x : R, B₀ * (A₀ * x) = A₀ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← c00, mul_assoc]
  have d01 : ∀ x : R, B₁ * (A₀ * x) = A₀ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← c01, mul_assoc]
  have d10 : ∀ x : R, B₀ * (A₁ * x) = A₁ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← c10, mul_assoc]
  have d11 : ∀ x : R, B₁ * (A₁ * x) = A₁ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← c11, mul_assoc]
  have e0 : ∀ x : R, A₀ * (A₀ * x) = x := fun x => by rw [← mul_assoc, hA0, one_mul]
  have e1 : ∀ x : R, A₁ * (A₁ * x) = x := fun x => by rw [← mul_assoc, hA1, one_mul]
  have hfour : (4 : R) = 1 + 1 + 1 + 1 := by norm_num
  simp only [chshOp]
  noncomm_ring
  simp only [d00, d01, d10, d11, e0, e1, hA0, hA1, hB0, hB1, mul_one]
  rw [hfour]
  abel

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
