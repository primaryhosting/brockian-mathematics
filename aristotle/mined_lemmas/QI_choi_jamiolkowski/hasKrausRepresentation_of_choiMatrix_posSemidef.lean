import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

lemma hasKrausRepresentation_of_choiMatrix_posSemidef
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : (choiMatrix Φ).PosSemidef) :
    HasKrausRepresentation Φ := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  refine ⟨fun c => Matrix.of fun a i => (starRingEnd ℂ) (B c (i, a)), fun X => ?_⟩
  ext a b
  rw [apply_entry_eq_choi, Matrix.sum_apply]
  simp only [kraus_term_entry, Matrix.of_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [sum_swap3]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [hB]
  simp [Matrix.mul_apply, Matrix.star_apply]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus representation is completely positive. -/
