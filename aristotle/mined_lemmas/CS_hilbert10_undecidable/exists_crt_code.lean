import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem exists_crt_code (x : ℕ → ℕ) (n b : ℕ) (hb : (n)! ∣ b)
    (hlt : ∀ i ≤ n, x i < 1 + (i + 1) * b) :
    ∃ a, ∀ i ≤ n, a % (1 + (i + 1) * b) = x i := by
  set s : ℕ → ℕ := fun i => 1 + (i + 1) * b with hs
  have hco : (List.range (n + 1)).Pairwise (Function.onFun Nat.Coprime s) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_range, Function.onFun, hs]
    have hjn : (j : ℕ) ≤ n := by have := j.2; simp at this; omega
    have hij' : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
    have hdvd : ((j : ℕ) + 1) - ((i : ℕ) + 1) ∣ b := by
      have h1 : (j : ℕ) - (i : ℕ) ∣ (n)! := by
        refine Nat.dvd_factorial ?_ ?_ <;> omega
      have h2 : ((j : ℕ) + 1) - ((i : ℕ) + 1) = (j : ℕ) - (i : ℕ) := by omega
      rw [h2]
      exact h1.trans hb
    simpa [Nat.add_comm] using Nat.coprime_mul_succ hdvd
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfList x s (List.range (n + 1)) hco
  refine ⟨k, fun i hi => ?_⟩
  have hmem : i ∈ List.range (n + 1) := by simp; omega
  calc k % (1 + (i + 1) * b) = k % s i := rfl
    _ = x i % s i := hk i hmem
    _ = x i := Nat.mod_eq_of_lt (hlt i hi)

/-! ### Polynomials, congruences and majorants -/

/-- Polynomials respect congruences of their arguments. -/
