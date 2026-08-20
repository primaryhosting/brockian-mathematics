import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix

/-- The **point group** of a molecule whose nuclei occupy the positions `S ⊆ ℝ³`:
the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the set of nuclear positions onto itself. -/

def pointGroup (S : Set (Fin 3 → ℝ)) : Subgroup (Matrix.orthogonalGroup (Fin 3) ℝ) where
  carrier := {A | (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) '' S = S}
  one_mem' := by
    simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq, Submonoid.coe_mul] at *
    rw [show (fun v => ((A : Matrix (Fin 3) (Fin 3) ℝ) * B).mulVec v)
          = (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) ∘
            (fun v => (B : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) by
      funext v; simp [Matrix.mulVec_mulVec]]
    rw [Set.image_comp, hB, hA]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hA]
    rw [← Set.image_comp]
    have : (fun v => ((A⁻¹ : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec v) ∘
        (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) = id := by
      funext v
      simp only [Function.comp_apply, id_eq, Matrix.mulVec_mulVec]
      rw [show ((A⁻¹ : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
          (A : Matrix (Fin 3) (Fin 3) ℝ) = ((A⁻¹ * A : Matrix.orthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) from rfl]
      simp
    rw [this, Set.image_id]

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

By construction `Chem.pointGroup S` is a subgroup of the orthogonal group `O(3)`; the
content of the theorem is its finiteness.  If the nuclei of the molecule form a finite
set `S` of points that spans `ℝ³` (a genuinely three-dimensional molecule), then an
element of the point group is determined by the permutation it induces on `S`, so the
point group embeds into the (finite) set of self-maps of `S`, and is therefore finite. -/
