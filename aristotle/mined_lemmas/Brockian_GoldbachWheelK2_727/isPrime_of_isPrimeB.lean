import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


theorem isPrime_of_isPrimeB {p : Nat} (h : isPrimeB p = true) : IsPrime p := by
  rw [isPrimeB] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    rcases hm with ⟨c, hc⟩
    omega
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  have hmle : m ≤ p := Nat.le_of_dvd (by omega) hm
  have : p % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hm
  exact noDivIn_spec p (p - 1) hnd m (by omega) (by omega) this

/-- The wheel: the primes below the modulus `727`, together with `727` itself.  These serve as
the pool of witnesses for the Goldbach decompositions. -/
