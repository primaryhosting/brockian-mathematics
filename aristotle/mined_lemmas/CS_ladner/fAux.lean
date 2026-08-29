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


noncomputable def fAux : Nat → Nat → Nat
  | 0 => fun _ => 0
  | (n + 1) => fun m =>
      if m ≤ n then fAux n m
      else fAux n n + (if defeated dec red K clock (fAux n) n then 1 else 0)

/-- The gap function of Ladner's construction. -/
