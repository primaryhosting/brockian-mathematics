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

noncomputable def omegaMat (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  (Matrix.of fun (_ : Unit) (p : n × n) => if p.1 = p.2 then (1 : ℂ) else 0)ᴴ *
    (Matrix.of fun (_ : Unit) (p : n × n) => if p.1 = p.2 then (1 : ℂ) else 0)

