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

theorem diagLang_not_mem_DTIME (t : ℕ → ℕ) : diagLang t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  set n := Nat.Partrec.Code.encodeCode c with hn
  have hdec : ofNat Nat.Partrec.Code n = c := by
    rw [hn, ← Nat.Partrec.Code.encodeCode_eq]
    exact Denumerable.ofNat_encode c
  have h := hc n
  rw [← diagBit_eq_ite] at h
  unfold diagBit at h
  rw [hdec] at h
  by_cases hc1 : evaln (t n) c n = some 1
  · rw [if_pos hc1] at h
    rw [h] at hc1
    simp at hc1
  · rw [if_neg hc1] at h
    exact hc1 h

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a larger time
bound `t'` such that strictly more languages are decidable in time `t'` than in time `t`.
The separating language is the diagonal language `diagLang t`. -/
