/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

lemma choi_posSemidef [Fintype A] [DecidableEq A] [Fintype B]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} (hCP : IsCompletelyPositive Φ) :
    (choi Φ).PosSemidef := by
  classical
  set n := Fintype.card A with hn
  set ε : Fin n ≃ A := (Fintype.equivFin A).symm with hε
  set w : Fin n × A → ℂ := fun p => if ε p.1 = p.2 then 1 else 0 with hw
  set Ω : Matrix (Fin n × A) (Fin n × A) ℂ :=
      (replicateCol Unit w) * (replicateCol Unit w)ᴴ with hΩ
  have hΩpsd : Ω.PosSemidef := posSemidef_self_mul_conjTranspose _
  have hampl := hCP n Ω hΩpsd
  have hEq : choi Φ = (ampliate Φ (Fin n) Ω).submatrix
      (fun p => (ε.symm p.1, p.2)) (fun p => (ε.symm p.1, p.2)) := by
    ext p q
    have key : (fun (i j : A) => Ω (ε.symm p.1, i) (ε.symm q.1, j)) = single p.1 q.1 (1 : ℂ) := by
      funext i j
      simp only [hΩ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply,
        Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, hw,
        Matrix.single_apply, Equiv.apply_symm_apply]
      by_cases h1 : p.1 = i <;> by_cases h2 : q.1 = j <;> simp [h1, h2]
    simp only [Matrix.submatrix_apply, ampliate, choi, key]
  rw [hEq]
  exact hampl.submatrix _

set_option linter.deprecated false in
/-- Kraus decomposition: a completely positive map is a sum of conjugations
`ρ ↦ ∑ s, K s * ρ * (K s)ᴴ`. -/
