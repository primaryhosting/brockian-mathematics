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

def noDivLe (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (d + 2) => (decide (n < (d + 2) * (d + 2)) || n % (d + 2) != 0) && noDivLe n (d + 1)

/-- A kernel-friendly primality test; it is correct for `n ≤ 1520`. -/

theorem noDivLe_spec :
    ∀ (k n d : Nat), noDivLe n k = true → 2 ≤ d → d ≤ k → d * d ≤ n → ¬ d ∣ n := by
  intro k
  induction k with
  | zero => intro n d _ h2 hd _; omega
  | succ k ih =>
    match k with
    | 0 => intro n d _ h2 hd _; omega
    | (k' + 1) =>
      intro n d h h2 hd hdd
      rw [noDivLe, Bool.and_eq_true] at h
      obtain ⟨h1, h2'⟩ := h
      by_cases hd' : d ≤ k' + 1
      · exact ih n d h2' h2 hd' hdd
      · have hde : d = k' + 2 := by omega
        subst hde
        rcases Bool.or_eq_true _ _ |>.mp h1 with hlt | hmod
        · exact absurd (of_decide_eq_true hlt) (by omega)
        · have hmod' : n % (k' + 2) ≠ 0 := by simpa using hmod
          rintro ⟨c, rfl⟩
          exact hmod' (Nat.mul_mod_right (k' + 2) c)
