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

theorem exists_TIME_of_computable {L : Language} (hL : Computable L) :
    ∃ t : ℕ → ℕ, L ∈ TIME t := by
  have hn : Computable fun x : ℕ => (if L x then 1 else 0 : ℕ) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Nat.Partrec.of_eq
    (Partrec.nat_iff.1 hn.partrec) (fun n => rfl))
  have hmem : ∀ x : ℕ, ∃ k, evaln k c x = some (if L x then 1 else 0) := by
    intro x
    have : (if L x then 1 else 0 : ℕ) ∈ eval c x := by
      rw [hc]; simp
    exact evaln_complete.1 this
  choose t ht using hmem
  exact ⟨t, c, ht⟩

/-- **Time hierarchy theorem.** For every computable time bound `f` there is a larger
time bound `g` such that the languages decidable in time `g` strictly contain those
decidable in time `f`: more time gives strictly more languages.

The witness separating the two classes is the diagonal language `CS.diag f`. -/
