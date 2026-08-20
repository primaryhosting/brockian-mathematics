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

theorem checkAll_spec :
    ∀ (k m : Nat), checkAll k = true → 2 ≤ m → m ≤ k → wheelOk m = true := by
  intro k
  induction k with
  | zero => intro m _ h2 hm; omega
  | succ k ih =>
    match k with
    | 0 => intro m _ h2 hm; omega
    | (k' + 1) =>
      intro m h h2 hm
      rw [checkAll, Bool.and_eq_true] at h
      by_cases hm' : m ≤ k' + 1
      · exact ih m h.2 h2 hm'
      · have hme : m = k' + 2 := by omega
        subst hme
        exact h.1

/-- The finite verification, checked by kernel reduction. -/
