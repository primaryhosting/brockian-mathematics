import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
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

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/-- The diagonal partial function associated with a candidate halting decider `H`:
on input `n`, it diverges when `H` claims that the `n`-th program halts on input `n`,
and returns `0` otherwise. -/

theorem halting_undecidable :
    ¬ ∃ H : Nat.Partrec.Code → ℕ → Bool,
        Computable₂ H ∧ ∀ (p : Nat.Partrec.Code) (x : ℕ), H p x = true ↔ (eval p x).Dom := by
  rintro ⟨H, hH, hspec⟩
  obtain ⟨e, he⟩ := exists_code.mp (partrec_diagFun hH)
  set n : ℕ := encode e with hn
  have hoe : ofNat Nat.Partrec.Code n = e := by
    simp [hn, Denumerable.ofNat_encode]
  have hval : eval e n = bif H e n then Part.none else Part.some 0 := by
    rw [he]
    simp [diagFun, hoe]
  by_cases hb : H e n = true
  · have hdom : (eval e n).Dom := (hspec e n).mp hb
    rw [hval, hb] at hdom
    exact hdom
  · have hb' : H e n = false := by simpa using hb
    have hdom : (eval e n).Dom := by
      rw [hval, hb']
      trivial
    exact hb ((hspec e n).mpr hdom)

/-- The same statement phrased with programs encoded as natural numbers: there is no
total computable `H : ℕ → ℕ → ℕ` such that `H p x = 1` exactly when the program with
index `p` halts on input `x`. -/
