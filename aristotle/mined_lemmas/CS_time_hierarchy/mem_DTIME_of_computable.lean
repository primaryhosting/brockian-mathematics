import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A language: a decision problem on natural-number-encoded inputs. -/
abbrev Lang := ℕ → Bool

/-- `DTIME f` is the class of languages `L` decided by some program (a code for a
partial recursive function) which, when run on input `n` with a budget of `f n`
computation steps (Kleene-style step-bounded evaluation `evaln`), halts and outputs
`1` if `n ∈ L` and `0` otherwise. -/

theorem mem_DTIME_of_computable (L : Lang) (hL : Computable L) : ∃ g : ℕ → ℕ, L ∈ DTIME g := by
  classical
  have hF : Computable fun n : ℕ => (if L n then 1 else 0 : ℕ) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hF.partrec)
  have hex : ∀ n, ∃ k, (if L n then 1 else 0 : ℕ) ∈ evaln k c n := by
    intro n
    refine evaln_complete.1 ?_
    rw [hcode]
    simp
  choose k hk using hex
  exact ⟨k, c, hk⟩

/-- **Time hierarchy theorem.**  For every computable time bound `f` there is a larger
time bound `g` such that strictly more languages can be decided in time `g` than in
time `f`: `DTIME f ⊊ DTIME g`.  The separating witness is the diagonal language
`diagLang f`, which by construction differs from the language of every program that
runs within time `f`. -/
