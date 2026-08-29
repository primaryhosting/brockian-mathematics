import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma adj_mul_Fm :
    ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) * Fm = Fm * Matrix.diagonal lam := by
  ext u k
  have hmv : (((SimpleGraph.cycleGraph 19).adjMatrix ℂ) * Fm) u k
      = ∑ v ∈ (SimpleGraph.cycleGraph 19).neighborFinset u, Fm v k := by
    rw [Matrix.mul_apply]
    have := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) u
      (fun v => Fm v k)
    simpa [Matrix.mulVec, dotProduct] using this
  rw [hmv, SimpleGraph.cycleGraph_neighborFinset (n := 17),
    Finset.sum_pair (by
      intro h
      rw [sub_eq_add_neg] at h
      exact absurd (add_left_cancel h) (by decide))]
  rw [Matrix.mul_diagonal, ← ec_add_ec_neg k]
  have e1 : (u - 1) * k = u * k + (-k) := by ring
  have e2 : (u + 1) * k = u * k + k := by ring
  simp only [Fm, e1, e2, ec_add]
  ring

/-- **Hückel theory for the C₁₉ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₉` is `∏_{k=0}^{18} (X - 2 cos (2πk/19))`; equivalently, the
adjacency eigenvalues of `C₁₉` are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
