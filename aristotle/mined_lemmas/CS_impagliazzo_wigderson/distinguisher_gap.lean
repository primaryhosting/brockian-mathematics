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

theorem distinguisher_gap {r s : Nat} {A : Nat → Bool} {gen : Nat → Nat} (h : s + 2 ≤ r)
    (hb : count s (fun y => A (gen y)) = 2 ^ s) (ha : count r A ≤ 2 ^ s) :
    ¬ 12 * (count s (fun y => A (gen y)) * 2 ^ r)
        ≤ 12 * (count r A * 2 ^ s) + 2 ^ r * 2 ^ s := by
  have hRS : 4 * 2 ^ s ≤ 2 ^ r := by
    have h1 : (2 : Nat) ^ (s + 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) h
    have h2 : (2 : Nat) ^ (s + 2) = 4 * 2 ^ s := by
      rw [Nat.pow_add]
      omega
    omega
  have hSpos : 0 < 2 ^ s := Nat.two_pow_pos _
  have hQ : 4 * (2 ^ s * 2 ^ s) ≤ 2 ^ s * 2 ^ r := by
    calc 4 * (2 ^ s * 2 ^ s) = 2 ^ s * (4 * 2 ^ s) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ 2 ^ s * 2 ^ r := Nat.mul_le_mul_left _ hRS
  have haS : count r A * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ ha
  have hbR : count s (fun y => A (gen y)) * 2 ^ r = 2 ^ s * 2 ^ r := by rw [hb]
  have hRSprod : 2 ^ r * 2 ^ s = 2 ^ s * 2 ^ r := Nat.mul_comm _ _
  have hPpos : 0 < 2 ^ s * 2 ^ s := Nat.mul_pos hSpos hSpos
  omega

/-- The fooling condition is a genuine restriction: no generator whose seed length is at
least two bits shorter than its output length can fool *all* tests.  The test that accepts
exactly the strings in the image of the generator distinguishes it from uniform.  Hence
restricting the fooling condition to polynomial-time tests, as in `PRG`, is essential. -/
