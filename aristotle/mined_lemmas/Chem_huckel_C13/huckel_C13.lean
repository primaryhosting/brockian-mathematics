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

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

theorem huckel_C13 :
    adjC13.charpoly =
      ∏ k ∈ Finset.range 13,
        (X - C (((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ))) := by
  rw [charpoly_eq_prod_zmod]
  exact Fin.prod_univ_eq_prod_range
    (fun m => (X - C (((2 * Real.cos (2 * Real.pi * (m : ℝ) / 13) : ℝ) : ℂ)))) 13

/-- Each of the 13 numbers `2 cos (2πk/13)` is an eigenvalue of the adjacency matrix
of `C₁₃`, with an explicit eigenvector. -/
