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


theorem gapF_mono (hcl : ∀ n, clock n ≤ n) :
    ∀ (m n : Nat), m ≤ n → gapF dec red K clock m ≤ gapF dec red K clock n := by
  intro m n
  induction n with
  | zero =>
      intro h
      have : m = 0 := by omega
      subst this
      exact Nat.le_refl _
  | succ k ih =>
      intro h
      by_cases hk : m ≤ k
      · have h1 := ih hk
        have h2 := gapF_le_succ dec red K clock hcl k
        omega
      · have : m = k + 1 := by omega
        subst this
        exact Nat.le_refl _

/-- If the gap function ever exceeds `v`, then it passes through the value `v`,
and at the input where it leaves the value `v` the defeat condition holds. -/
