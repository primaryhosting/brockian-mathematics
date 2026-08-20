/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

theorem maxEnt_posSemidef : (maxEnt n).PosSemidef := by
  have h : maxEnt n = (Matrix.of fun (_ : Unit) x => if x.1 = x.2 then (1 : ℂ) else 0)ᴴ *
      (Matrix.of fun (_ : Unit) x => if x.1 = x.2 then (1 : ℂ) else 0) := by
    ext x y
    simp only [maxEnt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> simp_all
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [DecidableEq m] in
/-- Applying `id_n ⊗ Φ` to the maximally entangled state gives exactly the Choi matrix. -/
