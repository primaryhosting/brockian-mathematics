/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

The model of computation is Mathlib's partial recursive `Nat.Partrec.Code`, whose
step-indexed evaluator `Nat.Partrec.Code.evaln k c n` runs the program `c` on input `n`
for `k` steps of fuel.  "Running time" is the amount of fuel consumed, and
`CS.DTIME t` is the class of languages decided within fuel `t n` on input `n`.

The theorem `CS.time_hierarchy` says: for every computable time bound `t` there is a
pointwise larger bound `t'` with `DTIME t ⊊ DTIME t'`, i.e. more time really does decide
strictly more languages.  The witness separating the two classes is the diagonal language
`CS.diagLang t = {n | the n-th program does not output 1 on input n within t n steps}`,
which is not in `DTIME t` by diagonalization, but is computable (because `evaln` is), hence
lies in `DTIME t'` for `t'` its own running time.
-/

open scoped Classical

open Nat.Partrec Nat.Partrec.Code Denumerable

namespace CS

/-- `DTIME t` is the class of languages `L ⊆ ℕ` decided within time bound `t`:
there is a program (a `Nat.Partrec.Code`) which, run on input `n` with `t n` steps of
fuel, halts and outputs `1` if `n ∈ L` and `0` otherwise.  Here "time" is measured by
the step-index (fuel) of Mathlib's step-indexed evaluator `Nat.Partrec.Code.evaln`. -/

theorem computable_diagBit {t : ℕ → ℕ} (ht : Computable t) : Computable (diagBit t) := by
  have he : Computable fun n => evaln (t n) (ofNat Nat.Partrec.Code n) n :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (((ht.pair (Primrec.ofNat Nat.Partrec.Code).to_comp)).pair Computable.id)
  have hb : Computable fun n => decide (evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1) :=
    Computable₂.comp (Primrec.eq (α := Option ℕ)).decide.to_comp he
      (Computable.const (some 1))
  exact (Computable.cond hb (Computable.const 0) (Computable.const 1)).of_eq fun n => by
    unfold diagBit; cases h : decide (evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1) <;>
      simp_all

/-- The diagonal language is not decidable within time `t`. -/
