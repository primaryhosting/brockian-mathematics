/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## What is proved here

Ladner's theorem: if `P ≠ NP`, then there is an `NP`-intermediate language, i.e.
a language that lies in `NP`, is not in `P`, and is not `NP`-complete.

Since Lean's mathematical library contains no model of resource-bounded
computation, the theorem is formulated over an abstract `CS.Framework`: a
bundle of the standard structural facts about the classes `P`, `NP`, about the
class `FP` of polynomial-time computable functions, and about the effective
enumerations of polynomial-time deciders and transducers.  Every field of
`CS.Framework` is a well-known true statement of complexity theory.

The proof is the usual delayed diagonalisation ("blowing holes in a hard
language"): starting from `L₀ ∈ NP \ P`, the language `holed = L₀ ∩ {x | the
stage at |x| is even}` is built, where the stage function is advanced by one
whenever a counterexample to the current requirement (either "the i-th
polynomial-time decider decides `holed`" or "the i-th polynomial-time function
reduces `L₀` to `holed`") turns up.  All of the mathematical content, namely
that the stage function must be unbounded and that consequently `holed` is
`NP`-intermediate, is proved here.

The single further assumption, `CS.Effectivity`, is the formal counterpart of
the standard informal step "the stage function can be computed in polynomial
time if it is advanced only as fast as a polynomial-time budget allows": it
asserts that the diagonalisation can be run along a slow schedule for which the
resulting set of hole lengths is polynomial-time decidable.  It says nothing
about the diagonalisation behaviour of the stage function, which is what is
proved below.

This file is deliberately independent of `Mathlib` (it uses only the Lean 4 core
prelude), so that the module docstring above can literally be the first thing in
the file.  A companion file `RequestProject/Main.lean` uses `Mathlib` to exhibit
a concrete `CS.Framework`, showing that the axioms bundled in `CS.Framework` are
consistent.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- Languages, i.e. sets of binary strings. -/
abbrev Lang := Str → Prop

/--
An abstract complexity-theoretic framework.

The fields record the standard (true) structural facts about the classes `P`,
`NP` and about the class `FP` of polynomial-time computable functions, together
with effective enumerations `dec` of the `P`-languages and `fn` of the
polynomial-time functions.
-/
structure Framework where
  /-- The class of polynomial-time decidable languages. -/
  P : Lang → Prop
  /-- The class of languages decidable in nondeterministic polynomial time. -/
  NP : Lang → Prop
  /-- The class of polynomial-time computable string functions. -/
  FP : (Str → Str) → Prop
  /-- An enumeration of (clocked) polynomial-time deciders. -/
  dec : Nat → Str → Bool
  /-- An enumeration of (clocked) polynomial-time transducers. -/
  fn : Nat → Str → Str
  /-- Every enumerated decider decides a language in `P`. -/
  dec_mem : ∀ i, P (fun x => dec i x = true)
  /-- Every language in `P` is decided by some enumerated decider. -/
  dec_complete : ∀ L, P L → ∃ i, ∀ x, (dec i x = true ↔ L x)
  /-- Every enumerated transducer is a polynomial-time function. -/
  fn_mem : ∀ i, FP (fn i)
  /-- Every polynomial-time function occurs in the enumeration. -/
  fn_complete : ∀ g, FP g → ∃ i, ∀ x, fn i x = g x
  /-- `P ⊆ NP`. -/
  P_subset_NP : ∀ L, P L → NP L
  /-- The empty language is in `P`. -/
  P_empty : P (fun _ => False)
  /-- `NP` is closed under intersection with `P`-languages. -/
  NP_inter_P : ∀ L H, NP L → P H → NP (fun x => L x ∧ H x)
  /-- `P` is closed under changing membership on strings of bounded length. -/
  P_of_agree : ∀ (L M : Lang) (N : Nat), P L → (∀ x : Str, N ≤ x.length → (M x ↔ L x)) → P M
  /-- `P` is closed downwards under polynomial-time many-one reductions. -/
  P_of_reduction :
    ∀ (L M : Lang) (g : Str → Str), FP g → (∀ x, L x ↔ M (g x)) → P M → P L

/-- Polynomial-time many-one reducibility. -/

theorem stage_unbounded_or_const (hs : ∀ m, s m ≤ m) :
    (∀ j, ∃ n, j ≤ stage F L₀ s n) ∨ ∃ N k, ∀ n, N ≤ n → stage F L₀ s n = k := by
  by_cases hc : ∃ N, ∀ n, N ≤ n → stage F L₀ s n = stage F L₀ s N
  · obtain ⟨N, hN⟩ := hc
    exact Or.inr ⟨N, stage F L₀ s N, hN⟩
  · refine Or.inl ?_
    have step : ∀ N, ∃ n, N ≤ n ∧ stage F L₀ s N < stage F L₀ s n := by
      intro N
      have hne : ¬ ∀ n, N ≤ n → stage F L₀ s n = stage F L₀ s N := fun h => hc ⟨N, h⟩
      apply Classical.byContradiction
      intro hno
      refine hne ?_
      intro n hn
      have h1 : ¬ (N ≤ n ∧ stage F L₀ s N < stage F L₀ s n) := fun hcc => hno ⟨n, hcc⟩
      have h2 := stage_mono (F := F) (L₀ := L₀) hs hn
      omega
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm1, hm2⟩ := step n
      exact ⟨m, by omega⟩

/-- The stage function is unbounded. -/
