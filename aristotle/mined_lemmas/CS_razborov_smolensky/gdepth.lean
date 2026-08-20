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


def gdepth (C : Circuit n) (i : Fin C.size) : ℕ :=
  match C.gate i with
  | .inp _ => 0
  | .cst _ => 0
  | .notg j => C.gdepth (C.up i j)
  | .org S => 1 + S.sup (fun j => C.gdepth (C.up i j))
  | .andg S => 1 + S.sup (fun j => C.gdepth (C.up i j))
  | .modg L => 1 + (L.map (fun j => C.gdepth (C.up i j))).foldr max 0
termination_by i.val
decreasing_by all_goals exact j.isLt

/-- The Boolean function computed by the circuit. -/
