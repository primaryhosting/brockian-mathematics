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


theorem foldr_max_eq_zero : ∀ l : List ℕ, (∀ a ∈ l, a = 0) → l.foldr max 0 = 0
  | [], _ => rfl
  | a :: l, h => by
      rw [List.foldr_cons, h a (by simp), foldr_max_eq_zero l (fun b hb => h b (by simp [hb]))]
      rfl

/-- The circuit consisting of a single `MOD q` gate applied to all `n` inputs. -/
