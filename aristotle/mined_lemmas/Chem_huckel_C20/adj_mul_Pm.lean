import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma adj_mul_Pm : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * Pm = Pm * Dm := by
  ext i k
  rw [Matrix.mul_apply, Dm, Matrix.mul_diagonal]
  have hterm : ∀ j : Fin 20, ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) i j * Pm j k
      = if j ∈ ({i - 1, i + 1} : Finset (Fin 20)) then Pm j k else 0 := by
    intro j
    simp only [SimpleGraph.adjMatrix_apply, Finset.mem_insert, Finset.mem_singleton, adj_iff]
    split <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair (sub_one_ne_add_one i)]
  simp only [Pm, Matrix.of_apply]
  rw [show (i - 1) * k = i * k - k by rw [sub_mul, one_mul],
    show (i + 1) * k = i * k + k by rw [add_mul, one_mul],
    ee_sub, ee_add]
  ring

