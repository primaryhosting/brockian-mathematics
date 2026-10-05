/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the file can literally begin with the header comment above.

Encoding conventions:
* an input of length `n` is a natural number `x` (thought of as the bit string
  `x.testBit 0, …, x.testBit (n-1)`);
* a random string of length `r` is a natural number `ρ < 2 ^ r`;
* probabilities are handled by counting: `count r f` is the number of strings of length `r`
  on which `f` returns `true`, and a probability statement `p ≥ 2/3` is written as
  `2 * 2 ^ r ≤ 3 * count r f`.
-/

namespace CS

/-! ## Counting -/

/-- The number of strings `ρ < 2 ^ r` on which `f` returns `true`. -/

theorem majority_of_accept {R S a b : Nat} (hR : 0 < R) (hS : 0 < S)
    (hacc : 2 * R ≤ 3 * a) (hfool : 12 * (a * S) ≤ 12 * (b * R) + R * S) : S < 2 * b := by
  -- multiply the acceptance bound by `S`
  have h1 : 2 * R * S ≤ 3 * a * S := Nat.mul_le_mul_right S hacc
  have h1' : 2 * (R * S) ≤ 3 * (a * S) := by
    simp only [Nat.mul_assoc] at h1
    exact h1
  -- hence `7 * (R * S) ≤ 12 * (b * R)`
  have h2 : 7 * (R * S) ≤ 12 * (b * R) := by omega
  have h3 : R * (7 * S) ≤ R * (12 * b) := by
    calc R * (7 * S) = 7 * (R * S) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 12 * (b * R) := h2
      _ = R * (12 * b) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
  have h4 : 7 * S ≤ 12 * b := Nat.le_of_mul_le_mul_left h3 hR
  omega

/-- If the rejection probability is at least `2/3` and the generator fools the algorithm
with advantage at most `1/12`, then at most half of the seeds are accepting. -/
