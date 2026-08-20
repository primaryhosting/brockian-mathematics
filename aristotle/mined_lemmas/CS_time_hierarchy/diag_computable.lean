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

theorem diag_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (diag f) := by
  have h1 : Computable fun x : ℕ => evaln (f x) (ofNat Code x) x :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (((hf.pair (Primrec.ofNat Code).to_comp)).pair Computable.id)
  have hb : Computable fun x : ℕ =>
      @BEq.beq (Option ℕ) instBEqOfDecidableEq (evaln (f x) (ofNat Code x) x) (some 1) :=
    Primrec.beq.to_comp.comp h1 (Computable.const (some 1))
  exact (Primrec.not.to_comp.comp hb).of_eq (fun x => by simp [diag, instBEqOfDecidableEq])

/-- Any computable language is decidable within some time bound. -/
