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

theorem diag_not_mem_DTIME (t : ℕ → ℕ) : diag t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  set n : ℕ := encode c with hn
  have hcode : ofNat Code n = c := by rw [hn, ofNat_encode]
  have hval : evaln (t n) c n = some (if diag t n then 1 else 0) := hc n
  have hd : diag t n = decide (evaln (t n) c n ≠ some 1) := by
    rw [diag, hcode]
  by_cases hb : diag t n
  · -- the language says "does not output 1", yet the program outputs 1
    have h1 : evaln (t n) c n = some 1 := by rw [hval, if_pos hb]
    rw [hd, h1] at hb
    simp at hb
  · -- the language says "outputs 1", yet the program outputs 0
    have h0 : evaln (t n) c n = some 0 := by
      rw [hval, if_neg hb]
    rw [hd, h0] at hb
    simp at hb

/-- The characteristic function of the diagonal language is computable, provided the time bound
is computable. -/
