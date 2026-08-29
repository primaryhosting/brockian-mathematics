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


theorem not_forall_exists {α : Sort _} {p : α → Prop} (h : ¬ ∀ a, p a) : ∃ a, ¬ p a :=
  Classical.byContradiction fun hh =>
    h fun a => Classical.byContradiction fun hp => hh ⟨a, hp⟩

/-- A `Nat`-valued function bounded by `N` attains a maximum value. -/
