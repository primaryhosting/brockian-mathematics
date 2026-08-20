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


theorem Deg_list_sum {F : Type*} [Field F] {e : ℕ} (l : List ((Fin n → Bool) → F))
    (hl : ∀ f ∈ l, f ∈ Deg F n e) : l.sum ∈ Deg F n e := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons]
      exact Submodule.add_mem _ (hl a (by simp)) (ih (fun f hf => hl f (by simp [hf])))

/-- The approximating function has low degree. -/
