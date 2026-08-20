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


theorem gpoly_andg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (S : Finset (Fin i.val)) (hg : C.gate i = .andg S) :
    gpoly F C q t ρ i = ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
        (1 - gpoly F C q t ρ (C.up i j))) ^ (q - 1)) := by rw [gpoly, hg]

