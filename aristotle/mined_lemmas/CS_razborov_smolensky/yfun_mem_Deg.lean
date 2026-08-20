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


theorem yfun_mem_Deg (ζ : F) (i : Fin n) : yfun ζ i ∈ Deg F n 1 := by
  have : yfun ζ i = (fun _ => (1 : F)) + (ζ - 1) • mono F {i} := by
    funext x
    simp only [yfun, mono_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : x i = true <;> simp [h]
  rw [this]
  exact Submodule.add_mem _ (Deg_const_mem 1) (Submodule.smul_mem _ _ (mono_mem_Deg (by simp)))

