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


theorem ymono_mem_AgreeDeg {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (h : (Fin (2 * m + 1) → Bool) → F) (hhD : h ∈ Deg F (2 * m + 1) D)
    (hh : ∀ x ∈ A, h x = ymono ζ univ x) (S : Finset (Fin (2 * m + 1))) :
    ymono ζ S ∈ AgreeDeg F A (m + D) := by
  by_cases hS : S.card ≤ m
  · exact mem_AgreeDeg_of_mem_Deg (mem_Deg_of_le (ymono_mem_Deg ζ S) (by omega))
  · push_neg at hS
    refine ⟨h * ymono ζ⁻¹ (univ \ S), ?_, ?_⟩
    · have hcard : (univ \ S).card ≤ m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      exact mem_Deg_of_le (Deg_mul hhD (mem_Deg_of_le (ymono_mem_Deg ζ⁻¹ (univ \ S)) hcard))
        (by omega)
    · intro x hx
      rw [Pi.mul_apply, hh x hx, ymono_mul_inv ζ hζ0]

/-- Hence every function agrees on `A` with a function of degree at most `m + D`. -/
