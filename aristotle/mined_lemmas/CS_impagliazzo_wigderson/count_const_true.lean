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

theorem count_const_true (r : Nat) : count r (fun _ => true) = 2 ^ r := by
  have h : count r (fun _ => true) = (List.range (2 ^ r)).length := by
    rw [count, List.countP_eq_length]
    intro a _
    rfl
  rw [h, List.length_range]

/-! ## Boolean circuits -/

/-- Boolean circuits (with constants, input bits, and `¬`, `∧`, `∨` gates). -/
inductive Circuit where
  | const : Bool → Circuit
  | var : Nat → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit

/-- The Boolean function computed by a circuit, on an input encoded as a natural number. -/
