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


theorem ymono_mem_Deg (ζ : F) (S : Finset (Fin n)) : ymono ζ S ∈ Deg F n S.card := by
  have := Deg_prod (F := F) (s := S) (f := fun i => yfun ζ i) (e := 1)
    (fun i _ => yfun_mem_Deg ζ i)
  simpa [ymono] using this

