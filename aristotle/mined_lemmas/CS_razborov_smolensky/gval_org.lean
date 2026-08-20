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


theorem gval_org (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size)
    (S : Finset (Fin i.val)) (hg : C.gate i = .org S) :
    C.gval q x i = S.sup (fun j => C.gval q x (C.up i j)) := by rw [gval, hg]

