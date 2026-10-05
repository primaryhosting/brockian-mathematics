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

theorem exists_time_bound {L : Language} (h : Computable fun n : ℕ => if L n then 1 else 0) :
    ∃ t' : ℕ → ℕ, L ∈ DTIME t' := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 h.partrec)
  have hex : ∀ n : ℕ, ∃ k : ℕ, evaln k c n = some (if L n then 1 else 0) := by
    intro n
    have hmem : (if L n then 1 else 0) ∈ c.eval n := by
      rw [hc]; simp
    obtain ⟨k, hk⟩ := evaln_complete.1 hmem
    exact ⟨k, hk⟩
  refine ⟨fun n => Nat.find (hex n), c, fun n => Nat.find_spec (hex n)⟩

/-- **Time hierarchy theorem** (diagonalization form).

For every computable time bound `t` there is a strictly larger time bound `t'` such that the
class of languages decidable in time `t` is a *strict* subclass of those decidable in time `t'`:
more time gives strictly more languages. The witness separating the two classes is the diagonal
language `CS.diag t`. -/
