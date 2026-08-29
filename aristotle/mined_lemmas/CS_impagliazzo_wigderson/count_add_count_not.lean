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

theorem count_add_count_not (r : Nat) (f : Nat → Bool) :
    count r f + count r (fun ρ => !f ρ) = 2 ^ r := by
  have h := List.length_eq_countP_add_countP (l := List.range (2 ^ r)) f
  have hf : (fun a => decide ¬ (f a = true)) = (fun a => !f a) := by
    funext a; cases f a <;> simp
  rw [hf, List.length_range] at h
  exact h.symm

