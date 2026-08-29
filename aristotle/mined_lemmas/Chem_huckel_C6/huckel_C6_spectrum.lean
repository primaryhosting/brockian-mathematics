import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

theorem huckel_C6_spectrum :
    spectrum ℝ ((SimpleGraph.cycleGraph 6).adjMatrix ℝ) =
      Set.range fun k : Fin 6 => 2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C6, Polynomial.IsRoot.def,
    Polynomial.eval_prod]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine ⟨k, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
    exact hk.symm
  · rintro ⟨k, rfl⟩
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp

end Chem

