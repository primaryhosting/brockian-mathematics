/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open ComplexConjugate

section LSM

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Momentum obstruction (core of the Lieb–Schultz–Mattis argument).**

If the translation operator `T` is an isometry, the twist operator `U` anticommutes with `T`
(this is the algebraic footprint of a *half-integer* spin per unit cell: the twist shifts the
momentum by `π`), and `ψ` is a translation eigenvector, then the twisted state `U ψ` is
orthogonal to `ψ`. -/

noncomputable def sigmaZ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![1, 0; 0, -1]

/-- The twist operator of the two-level example: the Pauli matrix `σ_x`. -/
