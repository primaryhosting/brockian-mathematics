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

def IsTP (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ ρ : Matrix n n ℂ, (Φ ρ).trace = ρ.trace

omit [Fintype n] [DecidableEq n] in
/-- Sanity check: the identity channel is completely positive, so the hypotheses of
`QI.stinespring` are satisfiable. -/
