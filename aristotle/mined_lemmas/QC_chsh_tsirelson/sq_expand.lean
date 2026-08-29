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
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to come before any module docstring, so this
header is written as an ordinary block comment.)
-/

import Mathlib

/-!
# Tsirelson's bound for the CHSH operator

Given a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C*-algebra `A` — four self-adjoint
involutions with each `Aᵢ` commuting with each `Bⱼ` — the CHSH operator

`C = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies `‖C‖ ≤ 2√2`.

The proof is the classical one: `C` is self-adjoint and
`C² = 4 + [A₀, A₁] · [B₁, B₀]`, whence `‖C‖² = ‖C²‖ ≤ 4 + 2·2 = 8`.

A corollary specializes this to bounded operators on a complex Hilbert space, where
the norm is the operator norm.
-/

namespace QC

open scoped Real

variable {A : Type*}

/-- The CHSH operator associated to four observables. -/

private lemma sq_expand {a₀ a₁ p m : A} (h0 : a₀ * a₀ = 1) (h1 : a₁ * a₁ = 1)
    (hp0 : p * a₀ = a₀ * p) (hp1 : p * a₁ = a₁ * p)
    (hm0 : m * a₀ = a₀ * m) (hm1 : m * a₁ = a₁ * m) :
    (a₀ * p + a₁ * m) * (a₀ * p + a₁ * m)
      = (p * p + m * m) + ((a₀ * a₁) * (p * m) + (a₁ * a₀) * (m * p)) := by
  rw [add_mul, mul_add, mul_add, mul_mul_mul_swap' hp0, mul_mul_mul_swap' hp1,
    mul_mul_mul_swap' hm0, mul_mul_mul_swap' hm1, h0, h1, one_mul, one_mul]
  abel

variable [StarRing A]

/-- The square of the CHSH operator: `C² = 4 + [A₀, A₁] · [B₁, B₀]`. -/
