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


theorem Deg_mul {d₁ d₂ : ℕ} {f g : (Fin n → Bool) → F} (hf : f ∈ Deg F n d₁)
    (hg : g ∈ Deg F n d₂) : f * g ∈ Deg F n (d₁ + d₂) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨T, hT, rfl⟩ := hg
          rw [mono_mul]
          exact mono_mem_Deg (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hS hT))
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

