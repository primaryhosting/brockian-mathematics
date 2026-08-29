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

theorem countP_eq_le_one (R v : Nat) : (List.range R).countP (fun ρ => v == ρ) ≤ 1 := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [List.range_succ, List.countP_append]
      by_cases h : v = R
      · simp [h]
        omega
      · simp [h]
        omega

/-- At most `l.length` strings lie in the image of `f` on `l`. -/
