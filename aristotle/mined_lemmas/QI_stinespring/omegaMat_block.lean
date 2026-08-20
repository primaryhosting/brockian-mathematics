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

lemma omegaMat_block (i j : n) :
    (Matrix.of fun a b => omegaMat n (i, a) (j, b)) = Matrix.single i j (1 : ℂ) := by
  ext a b
  simp [omegaMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- **Kraus decomposition.** A completely positive map between matrix algebras has the
form `ρ ↦ ∑ c, A c * ρ * (A c)ᴴ`. This is obtained from the positive semidefiniteness
of the Choi matrix `(id ⊗ Φ) |Ω⟩⟨Ω|`. -/
