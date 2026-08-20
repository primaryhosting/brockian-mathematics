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

/-!
# Undecidability of the halting problem

`CS.halting_undecidable` states that there is no total computable predicate `H` which,
given a program `c` (a code for a partial recursive function) and an input `x`, decides
whether `c` halts on `x`.  The proof is the usual diagonalization: from such an `H` one
builds a partial recursive function which diverges exactly when `H` says it halts, and
then evaluates it at (a code for) itself.
-/

open Nat.Partrec Nat.Partrec.Code

/-- **Undecidability of the halting problem.**  There is no total computable function
`H : Code → ℕ → Bool` such that `H c x = true` exactly when the program `c` halts on
input `x`. -/

theorem CS.halting_undecidable_nat :
    ¬ ∃ H : ℕ → ℕ → Bool,
        Computable₂ H ∧
          ∀ p x, H p x = true ↔
            (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code p) x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine CS.halting_undecidable ⟨fun c x => H (Encodable.encode c) x, ?_, ?_⟩
  · exact hH.comp (Computable.encode.comp Computable.fst) Computable.snd
  · intro c x
    simpa [Denumerable.ofNat_encode] using hspec (Encodable.encode c) x


