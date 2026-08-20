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


theorem Deg_subst {F : Type*} [Field F] {n p D : ℕ} {P : (Fin (n + p) → Bool) → F}
    (hP : P ∈ Deg F (n + p) D) (b : Fin p → Bool) :
    (fun x : Fin n → Bool => P (Fin.append x b)) ∈ Deg F n D := by
  classical
  induction hP using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      set S₁ : Finset (Fin n) := univ.filter (fun j => Fin.castAdd p j ∈ S) with hS₁def
      have hcard : S₁.card ≤ D := by
        refine le_trans (Finset.card_le_card_of_injOn (fun j => Fin.castAdd p j) ?_ ?_) hS
        · intro j hj
          have hj' : j ∈ S₁ := hj
          rw [hS₁def, Finset.mem_filter] at hj'
          exact hj'.2
        · intro a _ c _ hac
          exact Fin.castAdd_inj.mp hac
      have key : ∀ x : Fin n → Bool, mono F S (Fin.append x b)
          = (if (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) then (1 : F) else 0)
            * mono F S₁ x := by
        intro x
        rw [mono_apply, mono_apply]
        have hiff : (∀ i ∈ S, (Fin.append x b) i = true)
            ↔ (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) ∧ (∀ j ∈ S₁, x j = true) := by
          constructor
          · intro hall
            refine ⟨fun k hk => ?_, fun j hj => ?_⟩
            · have := hall _ hk
              rwa [Fin.append_right] at this
            · rw [hS₁def, Finset.mem_filter] at hj
              have := hall _ hj.2
              rwa [Fin.append_left] at this
          · rintro ⟨h1, h2⟩ i hi
            induction i using Fin.addCases with
            | left j =>
                rw [Fin.append_left]
                exact h2 j (by rw [hS₁def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩)
            | right k =>
                rw [Fin.append_right]
                exact h1 k hi
        by_cases hb : (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true)
        · by_cases hx : (∀ j ∈ S₁, x j = true)
          · rw [if_pos (hiff.2 ⟨hb, hx⟩), if_pos hb, if_pos hx, mul_one]
          · rw [if_neg (fun hc => hx (hiff.1 hc).2), if_pos hb, if_neg hx, mul_zero]
        · rw [if_neg (fun hc => hb (hiff.1 hc).1), if_neg hb, zero_mul]
      have heq : (fun x : Fin n → Bool => mono F S (Fin.append x b))
          = (if (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) then (1 : F) else 0)
            • mono F S₁ := by
        funext x; rw [key x]; rfl
      rw [heq]
      exact Submodule.smul_mem _ _ (mem_Deg_of_le (mono_mem_Deg (le_refl _)) hcard)
  | zero => exact Submodule.zero_mem _
  | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
  | smul c a _ ha => exact Submodule.smul_mem _ _ ha

/-- A polynomial is eventually dominated by `2^t`. -/
