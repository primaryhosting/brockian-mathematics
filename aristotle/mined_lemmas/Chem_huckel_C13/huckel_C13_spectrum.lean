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

theorem huckel_C13_spectrum :
    spectrum ℂ adjC13 =
      (fun k : ℕ => (((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ))) '' (Set.Iio 13) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C13]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_range, sub_eq_zero, Set.mem_image, Set.mem_Iio]
  exact ⟨fun ⟨k, hk, hz⟩ => ⟨k, hk, hz.symm⟩, fun ⟨k, hk, hz⟩ => ⟨k, hk, hz.symm⟩⟩

end Chem

