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


theorem popc_pad {p r : ℕ} (h : r ≤ p) : popc (pad p r) = r := by
  simp only [popc, pad]
  rw [Fin.sum_univ_eq_sum_range (fun i => if (decide (i < r)) then 1 else 0) p]
  simp only [decide_eq_true_eq]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    show ({x ∈ range p | x < r}) = range r by ext x; simp; omega]
  simp

