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


noncomputable def gval (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size) : Bool :=
  match C.gate i with
  | .inp j => x j
  | .cst b => b
  | .notg j => !(C.gval q x (C.up i j))
  | .org S => S.sup (fun j => C.gval q x (C.up i j))
  | .andg S => S.inf (fun j => C.gval q x (C.up i j))
  | .modg L => decide (¬ q ∣ (L.filter (fun j => C.gval q x (C.up i j))).length)
termination_by i.val
decreasing_by all_goals exact j.isLt

/-- The depth of gate `i`: the maximal number of unbounded fan-in gates on a path from an
input to `i`.  (Negation gates are free; this only makes the lower bound stronger.) -/
