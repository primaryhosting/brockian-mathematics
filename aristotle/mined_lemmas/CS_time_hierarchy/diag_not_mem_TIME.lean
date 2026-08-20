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

theorem diag_not_mem_TIME (f : ℕ → ℕ) : diag f ∉ TIME f := by
  rintro ⟨c, hc⟩
  set e := Encodable.encode c
  have he : (ofNat Code e) = c := Denumerable.ofNat_encode c
  have hx := hc e
  have hd : diag f e = decide (evaln (f e) c e ≠ some 1) := by
    simp [diag, he]
  by_cases h : evaln (f e) c e = some 1
  · rw [h] at hd
    simp at hd
    rw [hd] at hx
    simp [h] at hx
  · rw [hd] at hx
    simp [h] at hx

/-- The diagonal language is computable when the time bound is. -/
