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


theorem fAux_stable :
    ∀ (m k : Nat), k ≤ m → fAux dec red K clock m k = gapF dec red K clock k := by
  intro m
  induction m with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      intro k hk
      by_cases hkn : k ≤ n
      · simp only [fAux]
        rw [if_pos hkn]
        exact ih k hkn
      · have : k = n + 1 := by omega
        subst this
        rfl

