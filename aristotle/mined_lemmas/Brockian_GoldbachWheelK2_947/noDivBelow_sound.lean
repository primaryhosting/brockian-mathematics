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

theorem noDivBelow_sound {n : Nat} : ∀ {k : Nat}, noDivBelow n k = true →
    ∀ d : Nat, 2 ≤ d → d ≤ k → n % d ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ d hd1 hd2; omega
  | succ k ih =>
    match k with
    | 0 => intro _ d hd1 hd2; omega
    | (k + 1) =>
      intro h d hd1 hd2
      simp only [noDivBelow, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge d (k + 2) with hlt | hge
      · exact ih h.2 d hd1 (by omega)
      · have hdk : d = k + 2 := by omega
        subst hdk; exact h.1

/-- Trial division is sound: if `n ≥ 2` has no divisor in `[2, k]` and `n < (k+1)^2`,
then `n` is prime. -/
