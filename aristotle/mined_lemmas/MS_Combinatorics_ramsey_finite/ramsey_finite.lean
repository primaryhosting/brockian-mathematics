import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

theorem ramsey_finite (r s : ℕ) : ∃ N : ℕ, ∀ (f : Sym2 (Fin N) → Bool),
    (∃ A : Finset (Fin N), r ≤ A.card ∧ ∀ x ∈ A, ∀ y ∈ A, x ≠ y → f s(x,y) = true) ∨
    (∃ B : Finset (Fin N), s ≤ B.card ∧ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → f s(x,y) = false) := by
  obtain ⟨N, hN⟩ := ramsey_aux r s
  refine ⟨N, fun f => ?_⟩
  have hcard : N ≤ (Finset.univ : Finset (Fin N)).card := by simp
  rcases hN (Fin N) f Finset.univ hcard with ⟨A, _, hAcard, hAmono⟩ | ⟨B, _, hBcard, hBmono⟩
  · exact Or.inl ⟨A, hAcard, hAmono⟩
  · exact Or.inr ⟨B, hBcard, hBmono⟩

