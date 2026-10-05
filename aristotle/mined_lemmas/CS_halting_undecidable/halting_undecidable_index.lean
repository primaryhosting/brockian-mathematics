import Mathlib

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

/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Code Denumerable Encodable

/-- The diagonal partial function associated to a candidate halting decider `H`:
on input `n` it diverges exactly when `H` claims that the `n`-th program halts on
input `n`, and returns `0` otherwise. -/

theorem halting_undecidable_index :
    ¬ ∃ H : ℕ → ℕ → Bool,
        Computable₂ H ∧ ∀ (e x : ℕ), H e x = true ↔ ((ofNat Code e).eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine halting_undecidable ⟨fun p x => H (encode p) x, ?_, ?_⟩
  · exact hH.comp (Computable.encode.comp Computable.fst) Computable.snd
  · intro p x
    simpa [Denumerable.ofNat_encode] using hspec (encode p) x

end CS

