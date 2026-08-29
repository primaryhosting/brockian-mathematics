import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

/-- A comparison-based decision tree on `n` elements with results in `α`.
An internal node compares the elements at two positions and branches on the answer. -/
inductive DTree (n : ℕ) (α : Type u) where
  | leaf : α → DTree n α
  | node : Fin n → Fin n → DTree n α → DTree n α → DTree n α

namespace DTree

variable {n : ℕ} {α : Type u}

/-- Worst-case number of comparisons performed by the tree. -/

theorem perm_eq_of_le_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∀ i j, σ i ≤ σ j ↔ τ i ≤ τ j) : σ = τ := by
  have cardlt : ∀ a : Fin n, (Finset.univ.filter (fun m : Fin n => m < a)).card = a.val := by
    intro a
    rw [show (Finset.univ.filter (fun m : Fin n => m < a)) = Finset.Iio a by ext m; simp]
    exact Fin.card_Iio a
  have key : ∀ (ρ : Equiv.Perm (Fin n)) (i : Fin n),
      (Finset.univ.filter (fun k => ρ k < ρ i)).card = (ρ i).val := by
    intro ρ i
    have himg : (Finset.univ.filter (fun k => ρ k < ρ i))
        = (Finset.univ.filter (fun m : Fin n => m < ρ i)).image ρ.symm := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · exact fun hk => ⟨ρ k, hk, by simp⟩
      · rintro ⟨m, hm, rfl⟩; simpa using hm
    rw [himg, Finset.card_image_of_injective _ ρ.symm.injective, cardlt]
  ext i
  have hlt : ∀ k, σ k < σ i ↔ τ k < τ i := by
    intro k
    constructor <;> intro hk
    · exact lt_of_not_ge fun hc => absurd ((h i k).2 hc) (not_le.2 hk)
    · exact lt_of_not_ge fun hc => absurd ((h i k).1 hc) (not_le.2 hk)
  have h1 := key σ i
  rw [Finset.filter_congr (fun k _ => by simpa using hlt k), key τ i] at h1
  exact h1.symm

/-- The hypothesis of `sorting_lb_5` is satisfiable: the (wasteful) algorithm that performs
all 25 comparisons and returns the list of answers does determine the input ordering.
Hence the lower bound is not vacuous. -/
