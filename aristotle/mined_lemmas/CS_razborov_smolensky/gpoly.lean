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


noncomputable def gpoly (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) : (Fin n → Bool) → F :=
  match C.gate i with
  | .inp j => mono F {j}
  | .cst b => fun _ => ind F b
  | .notg j => 1 - gpoly F C q t ρ (C.up i j)
  | .org S => 1 - ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true), gpoly F C q t ρ (C.up i j)) ^ (q - 1))
  | .andg S => ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
        (1 - gpoly F C q t ρ (C.up i j))) ^ (q - 1))
  | .modg L => ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum) ^ (q - 1)
termination_by i.val
decreasing_by all_goals exact j.isLt

