/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

theorem GoldbachWheelK2_727 :
    ∀ n : Nat, n % 2 = 0 → 4 ≤ n → n ≤ 2 * 727 →
      ∃ p q : Nat, p ∈ goldbachWheelK2 ∧ IsPrime p ∧ IsPrime q ∧ p + q = n := by
  intro n hn h4 hle
  have hm : wheelOk (n / 2) = true :=
    checkAll_spec 727 (n / 2) checkAll_727 (by omega) (by omega)
  obtain ⟨p, hp, hpb⟩ := List.any_eq_true.mp hm
  rw [Bool.and_eq_true] at hpb
  obtain ⟨hp1, hp2⟩ := hpb
  have hple : p ≤ 181 := wheel_le_181 p hp
  have hn2 : 2 * (n / 2) = n := by omega
  rw [hn2] at hp2
  have hq2 : 2 ≤ n - p := isPrimeB_two_le hp2
  exact ⟨p, n - p, hp, isPrimeB_isPrime (by omega) hp1, isPrimeB_isPrime (by omega) hp2, by omega⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in
`RequestProject/GoldbachWheelK2_727.lean`, which is deliberately import-free (Lean requires
`import` lines to precede every other command, so the mandated header comment can only be the
first thing in a file that has no imports).

Here we connect the elementary primality predicate `Brockian.IsPrime` used there with Mathlib's
`Nat.Prime`, and restate the result in Mathlib's vocabulary.
-/

set_option maxHeartbeats 1000000

namespace Brockian

/-- `Brockian.IsPrime` agrees with Mathlib's `Nat.Prime`. -/
