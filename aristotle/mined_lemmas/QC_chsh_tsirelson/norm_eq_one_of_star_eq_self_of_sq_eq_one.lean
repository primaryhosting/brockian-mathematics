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

theorem norm_eq_one_of_star_eq_self_of_sq_eq_one {A : R} (hsa : star A = A) (hinv : A ^ 2 = 1) :
    ‖A‖ = 1 := by
  have h : ‖A‖ * ‖A‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hsa, ← pow_two, hinv, norm_one]
  nlinarith [norm_nonneg A]

/-- The commutator of two self-adjoint involutions has norm at most `2`. -/
