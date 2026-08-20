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

theorem hasKraus_of_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  classical
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h
  set e := (Fintype.equivFin (n × m)).symm with he
  refine ⟨Fintype.card (n × m), fun k => Matrix.of fun a i => star (B (e k) (i, a)), ?_⟩
  intro X
  ext a b
  rw [apply_eq_sum_choi Φ X a b]
  have hC : ∀ i j, choiMatrix Φ (i, a) (j, b) = ∑ p : n × m, star (B p (i, a)) * B p (j, b) := by
    intro i j
    rw [hB]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [hC, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Equiv.sum_comp e (fun p => ∑ j, ∑ i, star (B p (i, a)) * X i j * B p (j, b))]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2, t.2.1, t.1), fun s => (s.2.2, s.2.1, s.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ (fun t => by simp only [Equiv.coe_fn_mk]; ring)

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
