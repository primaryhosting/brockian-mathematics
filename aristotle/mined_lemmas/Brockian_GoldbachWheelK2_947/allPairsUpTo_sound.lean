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

theorem allPairsUpTo_sound : ∀ {m : Nat}, allPairsUpTo m = true →
    ∀ j : Nat, 2 ≤ j → j ≤ m → hasPair (2 * j) primeCands = true := by
  intro m
  induction m with
  | zero => intro _ j hj1 hj2; omega
  | succ m ih =>
    match m with
    | 0 => intro _ j hj1 hj2; omega
    | (m + 1) =>
      intro h j hj1 hj2
      simp only [allPairsUpTo, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge j (m + 2) with hlt | hge
      · exact ih h.2 j hj1 (by omega)
      · have hj : j = m + 2 := by omega
        subst hj; exact h.1

/-- The verified computation: every even number `2 * j` with `2 ≤ j ≤ 947` has a Goldbach
pair among `primeCands`. -/
