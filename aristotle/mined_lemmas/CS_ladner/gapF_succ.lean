/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: the required header comment
above is a module docstring, and Lean only accepts a module docstring at the
very beginning of a file when the file has no `import` commands.  Everything
below therefore uses only the Lean 4 core library.
-/

namespace CS

open Classical

/-- A language: a set of (encoded) strings, i.e. a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/-! ## Classical helpers -/


theorem gapF_succ (hcl : ∀ n, clock n ≤ n) (n : Nat) :
    gapF dec red K clock (n + 1) =
      gapF dec red K clock n +
        (if defeated dec red K clock (gapF dec red K clock) n then 1 else 0) := by
  have h1 : gapF dec red K clock (n + 1) = fAux dec red K clock (n + 1) (n + 1) := rfl
  rw [h1]
  simp only [fAux]
  rw [if_neg (by omega : ¬ (n + 1 ≤ n))]
  have h2 : ∀ k, k ≤ n → fAux dec red K clock n k = gapF dec red K clock k :=
    fAux_stable dec red K clock n
  rw [h2 n (Nat.le_refl n), defeated_congr dec red K clock (hcl n) h2]

