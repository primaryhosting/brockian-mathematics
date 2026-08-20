import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {ι : Type*} [Fintype ι]

/-- The set of probability vectors indexed by `ι`. -/

lemma convex_probSimplex : Convex ℝ (probSimplex ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hx.1 i
    have h2 := hy.1 i
    simpa using add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2]
    linarith

/-- The Gibbs entropy `−∑ pᵢ log pᵢ` is concave on the simplex of probability vectors. -/
