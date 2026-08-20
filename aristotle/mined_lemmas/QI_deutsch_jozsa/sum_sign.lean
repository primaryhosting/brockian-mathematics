import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

lemma sum_sign {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ x, sign (f x)
      = ((univ.filter fun x => f x = false).card : ℝ)
        - ((univ.filter fun x => f x = true).card : ℝ) := by
  classical
  have : ∑ x, sign (f x)
      = (∑ x ∈ univ.filter fun x => f x = true, sign (f x))
        + ∑ x ∈ univ.filter fun x => ¬ (f x = true), sign (f x) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [this]
  have h1 : (∑ x ∈ univ.filter fun x : Fin n → Bool => f x = true, sign (f x))
      = -((univ.filter fun x => f x = true).card : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℝ))]
    · simp
    · intro x hx
      simp only [Finset.mem_filter] at hx
      simp [sign, hx.2]
  have h2 : (∑ x ∈ univ.filter fun x : Fin n → Bool => ¬ (f x = true), sign (f x))
      = ((univ.filter fun x => f x = false).card : ℝ) := by
    have hset : (univ.filter fun x : Fin n → Bool => ¬ (f x = true))
        = univ.filter fun x => f x = false := by
      apply Finset.filter_congr
      intro x _
      cases hx : f x <;> simp_all
    rw [hset, Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro x hx
      simp only [Finset.mem_filter] at hx
      simp [sign, hx.2]
  rw [h1, h2]; ring

