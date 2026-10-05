import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

lemma card_filter_half (A : Finset (BV n)) (t a : BV n)
    (hA : ∀ x ∈ A, x + a ∈ A) (ha : dotp t a = 1) :
    2 * (A.filter (fun x => dotp t x = 0)).card = A.card := by
  classical
  have hsplit : (A.filter (fun x => dotp t x = 0)).card
      + (A.filter (fun x => ¬ dotp t x = 0)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hne : (A.filter (fun x => ¬ dotp t x = 0))
      = (A.filter (fun x => dotp t x = 1)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro h
      rcases QI.ZMod.two_cases (dotp t x) with h0 | h1
      · exact absurd h0 h
      · exact h1
    · intro h
      rw [h]
      decide
  rw [hne] at hsplit
  have hbij : (A.filter (fun x => dotp t x = 0)).card
      = (A.filter (fun x => dotp t x = 1)).card := by
    refine Finset.card_bij' (fun x _ => x + a) (fun x _ => x + a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hA x hx.1, ?_⟩
      rw [dotp_add_right, hx.2, ha, zero_add]
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hA x hx.1, ?_⟩
      rw [dotp_add_right, hx.2, ha]
      decide
    · intro x _
      simp [BV.add_add_cancel]
    · intro x _
      simp [BV.add_add_cancel]
  omega

/-- The hyperplane orthogonal to `s`. -/
