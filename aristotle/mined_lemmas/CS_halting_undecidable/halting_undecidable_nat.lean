/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to come first;
-- the same text is repeated below as a module docstring.)

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

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **The halting problem is undecidable.**

There is no total computable function `H : Code → ℕ → Bool` which, given (a code for)
a program `p` and an input `x`, decides whether `p` halts on `x`
(i.e. whether the partial function `eval p` is defined at `x`).

The proof reduces to Mathlib's `ComputablePred.halting_problem`, which states that for each
fixed input `n` the predicate `fun c => (eval c n).Dom` is not computable; that result in turn
is obtained from Rice's theorem, whose proof is the usual diagonalization / fixed-point
(Kleene recursion theorem) argument. -/

theorem halting_undecidable_nat :
    ¬ ∃ H : ℕ → ℕ → ℕ,
        Computable₂ H ∧
          ∀ (p x : ℕ), H p x = 1 ↔ (eval (Denumerable.ofNat Code p) x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine halting_undecidable ⟨fun p x => decide (H (Encodable.encode p) x = 1), ?_, ?_⟩
  · have h1 : Computable₂ fun (p : Code) (x : ℕ) => H (Encodable.encode p) x :=
      hH.comp (Computable.encode.comp (Computable.fst)) Computable.snd
    exact ((Primrec.eq.decide.comp _root_.Primrec.id
      (_root_.Primrec.const 1)).to_comp).comp h1
  · intro p x
    have h := hspec (Encodable.encode p) x
    simp only [Denumerable.ofNat_encode] at h
    simpa using h

end CS

#print axioms CS.halting_undecidable
#print axioms CS.halting_undecidable_nat

