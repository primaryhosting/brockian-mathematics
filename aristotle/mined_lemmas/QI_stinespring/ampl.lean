import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The partial trace over the second (ancilla) factor of a matrix indexed by a product. -/

noncomputable def ampl {n m : Type} (k : Type) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun a b => M (p.1, a) (q.1, b)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* if all its amplifications
`id_k ⊗ Φ` map positive semidefinite matrices to positive semidefinite matrices. -/
