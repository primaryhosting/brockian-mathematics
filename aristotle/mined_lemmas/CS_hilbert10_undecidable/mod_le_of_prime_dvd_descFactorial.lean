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

theorem mod_le_of_prime_dvd_descFactorial {P a u : ℕ} (hp : P.Prime) (hu : u < P)
    (h : P ∣ a.descFactorial (u + 1)) : a % P ≤ u := by
  rw [Nat.descFactorial_eq_prod_range] at h
  obtain ⟨j, hj, hdvd⟩ := (Nat.Prime.prime hp).dvd_finset_prod_iff _ |>.mp h
  simp only [Finset.mem_range] at hj
  rcases lt_or_ge a j with haj | haj
  · have : a % P = a := Nat.mod_eq_of_lt (by omega)
    omega
  · have hm : a ≡ j [MOD P] := ((Nat.modEq_iff_dvd' haj).mpr hdvd).symm
    have h2 : a % P = j % P := hm
    rw [h2, Nat.mod_eq_of_lt (by omega)]
    omega

/-- If all the factors `1 + (k+1) b`, `k < y`, divide `N`, then so does their product; the
hypothesis on `b` guarantees that these factors are pairwise coprime. -/
