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


theorem delta_mem_Deg (a : Fin n → Bool) : delta F a ∈ Deg F n n := by
  have hfact : ∀ i : Fin n,
      (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) ∈ Deg F n 1 := by
    intro i
    by_cases h : a i = true
    · have : (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) = mono F {i} := by
        funext x; simp [mono_apply, h]
      rw [this]; exact mono_mem_Deg (by simp)
    · have h' : a i = false := by simpa using h
      have : (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) = 1 - mono F {i} := by
        funext x; simp only [mono_apply, h', Pi.sub_apply, Pi.one_apply]
        cases hx : x i <;> simp [hx]
      rw [this]
      exact Submodule.sub_mem _ Deg_one_mem (mono_mem_Deg (by simp))
  have hprod := Deg_prod (F := F) (s := (univ : Finset (Fin n)))
    (f := fun i => (fun x : Fin n → Bool => if x i = a i then (1:F) else 0)) (e := 1)
    (fun i _ => hfact i)
  have heq :
      (∏ i ∈ (univ : Finset (Fin n)), (fun x : Fin n → Bool => if x i = a i then (1:F) else 0))
        = delta F a := by
    funext x
    simp only [Finset.prod_apply, delta]
    by_cases h : x = a
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [heq] at hprod
  simpa using hprod

