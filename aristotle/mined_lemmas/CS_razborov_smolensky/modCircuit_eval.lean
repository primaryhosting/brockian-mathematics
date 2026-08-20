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


theorem modCircuit_eval (q n : ℕ) (x : Fin n → Bool) :
    (modCircuit n).eval q x = ModFun q n x := by
  rw [Circuit.eval, Circuit.gval, modCircuit_gate_out]
  simp only []
  have hfil : (List.filter
        (fun j => (modCircuit n).gval q x ((modCircuit n).up (modCircuit n).out j))
        (List.finRange n))
      = List.filter (fun j : Fin n => x j) (List.finRange n) := by
    refine List.filter_congr ?_
    intro j _
    exact modCircuit_gval_inp q n x ((modCircuit n).up (modCircuit n).out j) j.isLt
  rw [hfil, list_length_filter_eq_sum]
  simp only [ModFun, popc, Fin.sum_univ_def]
  rfl

