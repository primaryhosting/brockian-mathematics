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

theorem countP_image_le (R : Nat) (l : List Nat) (f : Nat → Nat) :
    (List.range R).countP (fun ρ => l.any (fun y => f y == ρ)) ≤ l.length := by
  induction l with
  | nil => simp
  | cons y t ih =>
      have h1 : (List.range R).countP (fun ρ => (f y == ρ) || t.any (fun y => f y == ρ))
          ≤ (List.range R).countP (fun ρ => f y == ρ)
            + (List.range R).countP (fun ρ => t.any (fun y => f y == ρ)) :=
        countP_or_le _ _ _
      have h2 := countP_eq_le_one R (f y)
      simp only [List.any_cons, List.length_cons]
      omega

/-- A test that accepts all outputs of the generator but at most a `2 ^ s` fraction of all
strings violates the fooling condition, provided the seed is at least two bits shorter than
the output. -/
