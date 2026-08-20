import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem ymono_mul_inv (ζ : F) (hζ : ζ ≠ 0) (S : Finset (Fin n)) (x : Fin n → Bool) :
    ymono ζ (univ : Finset (Fin n)) x * ymono ζ⁻¹ (univ \ S) x = ymono ζ S x := by
  have h1 : ymono ζ (univ : Finset (Fin n)) = ymono ζ (univ \ S) * ymono ζ S := by
    rw [ymono, ymono, ymono, Finset.prod_sdiff (Finset.subset_univ S)]
  rw [h1]
  simp only [Pi.mul_apply]
  have h2 : ymono ζ (univ \ S) x * ymono ζ⁻¹ (univ \ S) x = 1 := by
    simp only [ymono, Finset.prod_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp only [yfun]
    cases h : x i <;> simp [hζ]
  calc ymono ζ (univ \ S) x * ymono ζ S x * ymono ζ⁻¹ (univ \ S) x
      = (ymono ζ (univ \ S) x * ymono ζ⁻¹ (univ \ S) x) * ymono ζ S x := by ring
    _ = ymono ζ S x := by rw [h2, one_mul]

/-- The submodule of functions that agree on `A` with a function of degree at most `d`. -/
