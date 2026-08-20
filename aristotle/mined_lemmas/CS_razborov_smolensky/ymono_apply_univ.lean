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


theorem ymono_apply_univ (ζ : F) (x : Fin n → Bool) :
    ymono ζ (univ : Finset (Fin n)) x = ζ ^ (popc x) := by
  simp only [ymono, Finset.prod_apply, popc, yfun]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases h : x i <;> simp

