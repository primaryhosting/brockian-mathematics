import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/

lemma maxEnt_posSemidef : (maxEnt n).PosSemidef := by
  have : maxEnt n = (Matrix.of fun (_ : Unit) (p : n × n) => (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ *
      (Matrix.of fun (_ : Unit) (p : n × n) => (if p.1 = p.2 then (1 : ℂ) else 0)) := by
    ext p q
    simp [maxEnt, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [DecidableEq m] in
