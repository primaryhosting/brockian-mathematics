import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma card_par (hn : 1 ≤ n) :
    (univ.filter (fun x : Q n => par x = true)).card = 2 ^ (n - 1) := by
  have hne : (∅ : Finset (Fin n)) ≠ univ := by
    intro h
    have : (⟨0, hn⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := by rw [h]; exact Finset.mem_univ _
    simp at this
  have h0 : ∑ x : Q n, sgn x = 0 := by
    have := sum_sgn_mono (∅ : Finset (Fin n)) hne
    simpa [mono] using this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Q n))
    (fun x : Q n => par x = true) sgn
  have hA : ∑ x ∈ univ.filter (fun x : Q n => par x = true), sgn x
      = -((univ.filter (fun x : Q n => par x = true)).card : ℝ) := by
    have hval : ∀ x ∈ univ.filter (fun x : Q n => par x = true), sgn x = -1 := by
      intro x hx
      rw [sgn_eq_of_par, if_pos (Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    ring
  have hB : ∑ x ∈ univ.filter (fun x : Q n => ¬ (par x = true)), sgn x
      = ((univ.filter (fun x : Q n => ¬ (par x = true))).card : ℝ) := by
    have hval : ∀ x ∈ univ.filter (fun x : Q n => ¬ (par x = true)), sgn x = 1 := by
      intro x hx
      rw [sgn_eq_of_par, if_neg (Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hA, hB, h0] at hsplit
  have hcards : (univ.filter (fun x : Q n => par x = true)).card
      + (univ.filter (fun x : Q n => ¬ (par x = true))).card = 2 ^ n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Q n))) (p := fun x : Q n => par x = true)
    simpa using this
  have heq : (univ.filter (fun x : Q n => par x = true)).card
      = (univ.filter (fun x : Q n => ¬ (par x = true))).card := by
    have : ((univ.filter (fun x : Q n => par x = true)).card : ℝ)
        = ((univ.filter (fun x : Q n => ¬ (par x = true))).card : ℝ) := by linarith
    exact_mod_cast this
  have hpow : (2 : ℕ) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  omega

/-- The alternating sum computes the size of the set where `f` differs from parity. -/
