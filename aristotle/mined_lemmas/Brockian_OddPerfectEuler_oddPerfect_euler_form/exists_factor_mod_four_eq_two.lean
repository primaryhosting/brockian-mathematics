/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma exists_factor_mod_four_eq_two {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (h : (∏ x ∈ s, f x) % 4 = 2) :
    ∃ x ∈ s, f x % 4 = 2 := by
  have heven : (∏ x ∈ s, f x) % 2 = 0 := by omega
  have hnot4 : ¬(4 ∣ ∏ x ∈ s, f x) := by omega
  have hex : ∃ x ∈ s, f x % 2 = 0 := by
    by_contra hall_odd
    push_neg at hall_odd
    have hall_odd' : ∀ x ∈ s, f x % 2 = 1 := fun x hx =>
      Nat.mod_two_ne_zero.mp (hall_odd x hx)
    have hprod_odd : (∏ x ∈ s, f x) % 2 = 1 := by
      have aux : ∀ t : Finset ι, (∀ x ∈ t, f x % 2 = 1) →
          (∏ x ∈ t, f x) % 2 = 1 := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s' ha ih =>
          simp [Finset.prod_insert ha]
          have ha_odd := ht a (Finset.mem_insert_self a s')
          have hs_odd := ih (fun x hx => ht x (Finset.mem_insert_of_mem hx))
          simp [Nat.mul_mod, ha_odd, hs_odd]
      exact aux s hall_odd'
    omega
  obtain ⟨x, hx, hfx_even⟩ := hex
  refine ⟨x, hx, ?_⟩
  have hfx_not4 : ¬(4 ∣ f x) := by
    intro h4
    apply hnot4
    exact dvd_trans h4 (Finset.dvd_prod_of_mem _ hx)
  omega

