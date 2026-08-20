import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
it applies `Φ` to each `n × n` block of a `(k × n) × (k × n)` matrix. -/

theorem id_isCP : IsCP (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro k _ M hM
  have h : amplify (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) k M = M := by
    ext p q; simp [amplify]
  rw [h]; exact hM

omit [DecidableEq n] in
/-- Sanity check: the identity channel is trace preserving. -/
