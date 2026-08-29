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


theorem exists_max : ∀ (N : Nat) (g : Nat → Nat), (∀ n, g n ≤ N) → ∃ n0, ∀ n, g n ≤ g n0 := by
  intro N
  induction N with
  | zero =>
      intro g h
      exact ⟨0, fun n => by have h1 := h n; have h2 := h 0; omega⟩
  | succ N ih =>
      intro g h
      by_cases hc : ∀ n, g n ≤ N
      · exact ih g hc
      · obtain ⟨m, hm⟩ := not_forall_exists hc
        refine ⟨m, fun n => ?_⟩
        have h1 := h n
        omega

/-! ## Ladner's construction

Fix an enumeration `dec` of the polynomial-time deciders, an enumeration `red`
of the polynomial-time computable functions, a language `K`, and a *clock*
`clock : Nat → Nat` (in the intended instantiation, `clock n` is roughly
`log n`; the two requirements on it are that `clock n ≤ n`, which keeps the
construction well-founded and makes it polynomial-time computable, and that it
is nondecreasing and unbounded).

The gap function `gapF` is built stage by stage: at input `n` the current stage
is `gapF n`.  An even stage `2 * i` is devoted to diagonalising against the
`i`-th polynomial-time decider, and an odd stage `2 * i + 1` to killing the
`i`-th candidate reduction of `K` to the constructed language; the stage
advances as soon as a witness of failure is spotted inside the clock bound. -/

section Construction

variable (dec : Nat → Nat → Bool) (red : Nat → Nat → Nat) (K : Lang) (clock : Nat → Nat)

/-- The "defeat" condition of Ladner's blow-hole construction, evaluated at
input `n` for the stage `g n`.  All queries made by the condition are at
arguments `≤ clock n ≤ n`, so it only depends on the values of `g` on
`[0, n]`. -/
