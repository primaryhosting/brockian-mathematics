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

theorem minority_of_reject {R S a b : Nat} (hR : 0 < R)
    (hrej : 3 * a ≤ R) (hfool : 12 * (b * R) ≤ 12 * (a * S) + R * S) : 2 * b ≤ S := by
  have h1 : 3 * a * S ≤ R * S := Nat.mul_le_mul_right S hrej
  have h1' : 3 * (a * S) ≤ R * S := by
    simp only [Nat.mul_assoc] at h1
    exact h1
  have h2 : 12 * (b * R) ≤ 5 * (R * S) := by omega
  have h3 : R * (12 * b) ≤ R * (5 * S) := by
    calc R * (12 * b) = 12 * (b * R) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 5 * (R * S) := h2
      _ = R * (5 * S) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
  have h4 : 12 * b ≤ 5 * S := Nat.le_of_mul_le_mul_left h3 hR
  omega

/-! ## Derandomization -/

/-- **Key step.**  If a polynomial-time randomized algorithm `A` decides `L` with error at
most `1/3`, and a pseudorandom generator for the model exists, then `L` is in `P`: the
majority vote of `A` over all seeds of the generator computes `L`, and it runs in
polynomial time. -/
