import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma adj_mul_Pm : ((cycleGraph 15).adjMatrix ℂ) * Pm = Pm * Dm := by
  ext i l
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  have h1 : (((cycleGraph 15).adjMatrix ℂ) * Pm) i l
      = ∑ j ∈ (cycleGraph 15).neighborFinset i, Pm j l := by
    have : (((cycleGraph 15).adjMatrix ℂ) * Pm) i l
        = (((cycleGraph 15).adjMatrix ℂ) *ᵥ (fun j => Pm j l)) i := rfl
    rw [this, SimpleGraph.adjMatrix_mulVec_apply]
  rw [h1, show (cycleGraph 15).neighborFinset i = {i - 1, i + 1} from
      SimpleGraph.cycleGraph_neighborFinset (n := 13), Finset.sum_pair hne,
    Dm, Matrix.mul_diagonal]
  have e1 : Pm (i + 1) l = Pm i l * g l := by
    simp only [Pm, Matrix.of_apply, g_add, g_one, mul_pow]
    rfl
  have e2 : Pm (i - 1) l = Pm i l * (g l)⁻¹ := by
    simp only [Pm, Matrix.of_apply, g_sub_one, mul_pow, inv_pow]
    rfl
  rw [e1, e2]
  ring

