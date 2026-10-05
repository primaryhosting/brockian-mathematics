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

lemma sum_sq_amp {β : Type*} [DecidableEq β] (f : BV n → β) (c : BV n → ℝ) :
    ∑ z ∈ Finset.image f Finset.univ, (∑ x : BV n, (if f x = z then c x else 0)) ^ 2
      = ∑ x : BV n, ∑ x' : BV n, (if f x = f x' then c x * c x' else 0) := by
  classical
  have hstep : ∀ z, (∑ x : BV n, (if f x = z then c x else 0)) ^ 2
      = ∑ x : BV n, ∑ x' : BV n,
        (if f x = z then c x else 0) * (if f x' = z then c x' else 0) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [Finset.sum_eq_single (f x)]
  · by_cases h : f x = f x'
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _ hz
    simp [Ne.symm hz]
  · intro hx
    exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ x)) hx

/-- **Simon's quantum measurement.**  For a Simon function `f` with hidden shift `s`, one
query produces the uniform distribution on the hyperplane `s^⊥`: the outcome `y` has
probability `2 / 2^n = 2^{-(n-1)}` if `y ⬝ s = 0`, and probability `0` otherwise. -/
