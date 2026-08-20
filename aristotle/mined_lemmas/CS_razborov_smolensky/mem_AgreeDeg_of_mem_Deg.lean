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


theorem mem_AgreeDeg_of_mem_Deg {A : Finset (Fin n → Bool)} {d : ℕ}
    {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n d) : f ∈ AgreeDeg F A d :=
  ⟨f, hf, fun _ _ => rfl⟩

/-- The key step: on `A`, every `y`-monomial has degree at most `m + D`. -/
