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

lemma card_perp_filter {s t : BV n} (ht0 : t ≠ 0) (hts : t ≠ s) :
    2 * ((perp s).filter (fun y => dotp t y = 0)).card = (perp s).card := by
  classical
  obtain ⟨a, ha, ha'⟩ : ∃ a : BV n, dotp s a = 0 ∧ dotp t a = 1 := by
    by_contra hc
    push_neg at hc
    have hall : ∀ y : BV n, dotp s y = 0 → dotp t y = 0 := by
      intro y hy
      rcases QI.ZMod.two_cases (dotp t y) with h0 | h1
      · exact h0
      · exact absurd h1 (hc y hy)
    rcases eq_zero_or_eq_of_forall_dotp hall with h | h
    · exact ht0 h
    · exact hts h
  refine card_filter_half _ t a ?_ ha'
  intro x hx
  rw [mem_perp] at hx ⊢
  rw [dotp_add_right, hx, ha, add_zero]

/-- **Failure probability of Simon's algorithm.**  Out of the `|s^⊥|^m` equally likely
sample sequences, at most a `2^n / 2^m` fraction fails to determine the hidden shift. -/
