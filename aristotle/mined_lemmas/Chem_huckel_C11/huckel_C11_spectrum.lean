import Mathlib

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

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/

theorem huckel_C11_spectrum :
    spectrum ℂ ((cycleGraph 11).adjMatrix ℂ) =
      Set.range fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]
  exact exists_congr fun _ =>
    ⟨fun h => (sub_eq_zero.mp h).symm, fun h => by rw [h, sub_self]⟩

end Chem

