import Mathlib
/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The time hierarchy theorem, by diagonalization, in the step-indexed model of
computation provided by Mathlib's Gödel-numbered partial recursive functions
(`Nat.Partrec.Code`) together with its step-indexed evaluator
`Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ`.

For a time bound `t : ℕ → ℕ`, `CS.TIME t` is the set of languages `L : ℕ → Bool`
for which some code `c` outputs `L x` on input `x` within `t x` steps.

The main theorem `CS.time_hierarchy` states: for every computable time bound `f`
there is a larger time bound `g` with `TIME f ⊊ TIME g`; i.e. more time gives
strictly more languages.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Denumerable

/-- A language: a decision problem on the natural numbers. -/
abbrev Language := ℕ → Bool

/-- `TIME t` is the class of languages decided within `t x` steps on input `x`,
where a step budget is measured by Mathlib's step-indexed evaluator `evaln`. -/

theorem TIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) : TIME t₁ ⊆ TIME t₂ := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun x => evaln_mono (h x) (hc x)⟩

/-- The diagonal language for a time bound `f`: on input `x`, run the `x`-th code on
input `x` for `f x` steps, and output the opposite answer. -/
