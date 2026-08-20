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

theorem computable_diagLang (hf : Computable f) : Computable (diagLang f) := by
  have h1 : Computable fun n : ℕ => evaln (f n) (Denumerable.ofNat Code n) n :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (((hf.pair (Computable.ofNat Code)).pair Computable.id))
  have h2 : Computable fun n : ℕ =>
      decide (evaln (f n) (Denumerable.ofNat Code n) n = some 1) :=
    (Primrec₂.to_comp Primrec.eq.decide).comp h1 (Computable.const (some 1))
  have h3 := (Primrec.not.to_comp).comp h2
  exact h3.of_eq fun n => by simp [diagLang, decide_not]

end

/-- Completeness of the model: every computable language is decided within *some*
time bound, so the classes `DTIME f` are not vacuous. -/
