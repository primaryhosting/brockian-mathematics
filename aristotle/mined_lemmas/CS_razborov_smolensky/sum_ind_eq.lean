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


theorem sum_ind_eq {F : Type*} [Field F] {k : ℕ} (S : Finset (Fin k)) (sel w : Fin k → Bool) :
    ∑ j ∈ S.filter (fun j => sel j = true), ind F (w j)
      = ((S.filter (fun j => sel j = true ∧ w j = true)).card : F) := by
  simp only [ind]
  rw [Finset.sum_boole]
  congr 2
  rw [Finset.filter_filter]

/-- In characteristic `q`, the product `∏ (1 - cₖ^{q-1})` detects whether all `cₖ` are
divisible by `q`. -/
