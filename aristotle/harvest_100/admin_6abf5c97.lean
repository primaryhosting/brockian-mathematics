import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Setup

We work with the standard Mathlib model of computation: partial recursive functions
presented by codes (`Nat.Partrec.Code`), together with the step-indexed evaluation
function `Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ`.  `evaln k c n` runs the
machine `c` on input `n` for `k` steps, returning `some v` if it halts with output `v`
within that budget and `none` otherwise.

A *language* is a decidable subset of `ℕ`, represented as a function `ℕ → Bool`, and
`DTIME t` is the class of languages decided by some machine within `t n` steps on
input `n`.

The time hierarchy theorem then says: for every computable time bound `t` there is a
larger time bound `t'` with `DTIME t ⊊ DTIME t'`, i.e. more time gives strictly more
languages.  The separating language is the diagonal language.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A language: a decision predicate on the natural numbers. -/
abbrev Language := ℕ → Bool

/-- `DTIME t` is the class of languages `L` for which there is a machine (code) that,
on every input `n`, halts within `t n` steps and outputs `1` if `n ∈ L` and `0`
otherwise. -/
def DTIME (t : ℕ → ℕ) : Set Language :=
  {L | ∃ c : Code, ∀ n, evaln (t n) c n = some (if L n then 1 else 0)}

/-- More time can only help: `DTIME` is monotone in the time bound. -/
theorem DTIME_mono {t t' : ℕ → ℕ} (h : ∀ n, t n ≤ t' n) : DTIME t ⊆ DTIME t' := by
  rintro L ⟨c, hc⟩
  refine ⟨c, fun n => ?_⟩
  exact Option.mem_def.mp (evaln_mono (h n) (Option.mem_def.mpr (hc n)))

/-- The diagonal language for the time bound `t`: the input `n` is accepted exactly
when the `n`-th machine, run on input `n` for `t n` steps, fails to output `1`. -/
def diag (t : ℕ → ℕ) : Language :=
  fun n => decide (evaln (t n) (Denumerable.ofNat Code n) n ≠ some 1)

/-- Diagonalization: the diagonal language is not decidable in time `t`. -/
theorem diag_notMem_DTIME (t : ℕ → ℕ) : diag t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  have hn : Denumerable.ofNat Code (Encodable.encode c) = c := Denumerable.ofNat_encode c
  have h := hc (Encodable.encode c)
  by_cases hd : diag t (Encodable.encode c) = true
  · have hne : evaln (t (Encodable.encode c)) c (Encodable.encode c) ≠ some 1 := by
      have := hd
      rw [diag, decide_eq_true_iff, hn] at this
      exact this
    rw [if_pos hd] at h
    exact hne h
  · simp only [Bool.not_eq_true] at hd
    have heq : evaln (t (Encodable.encode c)) c (Encodable.encode c) = some 1 := by
      have := hd
      rw [diag, decide_eq_false_iff_not, not_not, hn] at this
      exact this
    rw [if_neg (by simp [hd]), heq] at h
    exact absurd h (by simp)

/-- The diagonal language is computable, provided the time bound is. -/
theorem diag_computable (t : ℕ → ℕ) (ht : Computable t) : Computable (diag t) := by
  have h1 : Computable (fun n => evaln (t n) (Denumerable.ofNat Code n) n) :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hEq : Computable (fun p : Option ℕ × Option ℕ => decide (p.1 = p.2)) := by
    obtain ⟨_, h⟩ := Primrec.eq (α := Option ℕ)
    exact h.to_comp.of_eq (fun p => by congr)
  have h2 : Computable
      (fun n => decide (evaln (t n) (Denumerable.ofNat Code n) n = some 1)) :=
    hEq.comp (h1.pair (Computable.const (some 1)))
  exact (Primrec.not.to_comp.comp h2).of_eq (fun n => by simp [diag, decide_not])

/-- Every computable language lies in `DTIME t'` for some (not necessarily computable)
time bound `t'`: simply take enough steps on each input. -/
theorem exists_time_of_computable {L : Language} (hL : Computable L) :
    ∃ t' : ℕ → ℕ, L ∈ DTIME t' := by
  have hF : Computable (fun n => if L n then 1 else 0) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hF.partrec)
  have key : ∀ n, ∃ k, (if L n then 1 else 0) ∈ evaln k c n := by
    intro n
    refine evaln_complete.mp ?_
    rw [hcode]
    simp
  refine ⟨fun n => Classical.choose (key n), c, fun n => ?_⟩
  exact Option.mem_def.mp (Classical.choose_spec (key n))

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a time
bound `t'` such that strictly more languages can be decided in time `t'` than in time
`t`: `DTIME t ⊊ DTIME t'`.  The witness separating the two classes is the diagonal
language `diag t`. -/
theorem time_hierarchy (t : ℕ → ℕ) (ht : Computable t) :
    ∃ t' : ℕ → ℕ, DTIME t ⊂ DTIME t' := by
  obtain ⟨s, hs⟩ := exists_time_of_computable (diag_computable t ht)
  refine ⟨fun n => max (t n) (s n), ?_⟩
  rw [Set.ssubset_iff_of_subset (DTIME_mono fun n => le_max_left _ _)]
  exact ⟨diag t, DTIME_mono (fun n => le_max_right _ _) hs, diag_notMem_DTIME t⟩

end CS

