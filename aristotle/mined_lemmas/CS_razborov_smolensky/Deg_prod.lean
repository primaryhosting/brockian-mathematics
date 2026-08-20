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


theorem Deg_prod {ι : Type*} {s : Finset ι} {f : ι → (Fin n → Bool) → F} {e : ℕ}
    (hf : ∀ i ∈ s, f i ∈ Deg F n e) : (∏ i ∈ s, f i) ∈ Deg F n (s.card * e) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Deg_one_mem : (1 : (Fin n → Bool) → F) ∈ Deg F n 0)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : f a ∈ Deg F n e := hf a (by simp)
      have h2 : (∏ i ∈ s, f i) ∈ Deg F n (s.card * e) :=
        ih (fun i hi => hf i (by simp [hi]))
      have := Deg_mul h1 h2
      have he : e + s.card * e = (s.card + 1) * e := by ring
      rwa [he] at this

