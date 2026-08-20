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


theorem Deg_sum {ι : Type*} {s : Finset ι} {f : ι → (Fin n → Bool) → F} {e : ℕ}
    (hf : ∀ i ∈ s, f i ∈ Deg F n e) : (∑ i ∈ s, f i) ∈ Deg F n e :=
  Submodule.sum_mem _ hf

/-- The indicator function of a point of the cube. -/
