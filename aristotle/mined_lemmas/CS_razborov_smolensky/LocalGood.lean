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


def LocalGood (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (x : Fin n → Bool) (i : Fin C.size) : Prop :=
  (∀ j : Fin i.val, Good F C q t ρ x (C.up i j)) → Good F C q t ρ x i

