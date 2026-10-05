import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
# Goldbach Wheel K 2 947 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_947` lives in the self-contained file
`RequestProject/GoldbachWheelK2_947.lean` (which carries no imports, since its header
comment must be the first thing in the file). Here we identify the primality notion used
there with Mathlib's `Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem hasPair_sound {n : Nat} (hn : n ≤ 2024) :
    ∀ L : List Nat, hasPair n L = true → GoldbachK2 n := by
  intro L
  induction L with
  | nil => intro h; simp [hasPair] at h
  | cons p ps ih =>
    intro h
    simp only [hasPair, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hple, hp⟩, hq⟩ | h
    · exact ⟨p, n - p, isPrimeB_sound (by omega) hp, isPrimeB_sound (by omega) hq, by omega⟩
    · exact ih h

/-- `allPairsUpTo m = true` iff `hasPair (2 * j) primeCands` holds for all `2 ≤ j ≤ m`. -/
