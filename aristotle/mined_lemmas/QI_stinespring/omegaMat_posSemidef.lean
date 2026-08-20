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

lemma omegaMat_posSemidef : (omegaMat n).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The `(i, j)`-block of `|Ω⟩⟨Ω|` is the matrix unit `Eᵢⱼ`. -/
