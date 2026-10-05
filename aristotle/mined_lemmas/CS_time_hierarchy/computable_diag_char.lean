import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

/-- A language: a decision problem whose instances are encoded as natural numbers. -/
abbrev Language : Type := ℕ → Bool

/-- `DTIME t` is the class of languages decided by some partial recursive program
(a `Nat.Partrec.Code`) within `t n` steps on input `n`, where "steps" is measured by the
step-indexed evaluator `Nat.Partrec.Code.evaln`: the machine must output `1` on inputs in the
language and `0` on inputs outside it, using at most `t n` fuel. -/

theorem computable_diag_char {t : ℕ → ℕ} (ht : Computable t) :
    Computable (fun n : ℕ => if diag t n then 1 else 0) := by
  have heqp : Primrec fun p : Option ℕ × Option ℕ => decide (p.1 = p.2) := by
    obtain ⟨_, h⟩ := (Primrec.eq (α := Option ℕ))
    exact h.of_eq fun p => by simp
  have hev : Computable fun n : ℕ => evaln (t n) (ofNat Code n) n :=
    primrec_evaln.to_comp.comp
      ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hd : Computable fun n : ℕ => decide (evaln (t n) (ofNat Code n) n = some 1) :=
    heqp.to_comp.comp (hev.pair (Computable.const (some 1)))
  have hcond := Computable.cond hd (Computable.const (0 : ℕ)) (Computable.const 1)
  exact hcond.of_eq fun n => by
    by_cases h : evaln (t n) (ofNat Code n) n = some 1 <;> simp [diag, h]

/-- A computable language lies in `DTIME t'` for some time bound `t'`. -/
