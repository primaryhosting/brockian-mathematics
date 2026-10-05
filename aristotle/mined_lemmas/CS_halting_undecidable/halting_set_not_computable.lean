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

set_option grind.warning false

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Undecidability of the halting problem.**

There is no total computable function `H` which, given (a code for) a program `p`
and an input `x`, decides whether `p` halts on `x`.

Programs are the partial recursive `Nat.Partrec.Code`s, whose semantics is
`Nat.Partrec.Code.eval : Code → ℕ →. ℕ`; "`p` halts on `x`" is `(p.eval x).Dom`.
Totality of `H` is built into its type `Code → ℕ → Bool`, and computability is
`Computable₂ H`.

The proof is Turing's diagonal argument: from such an `H` one builds the
partial recursive function that, on input `n`, diverges exactly when the
program coded by `n` halts on `n`; feeding a code of this function to itself
yields a contradiction. -/

theorem halting_set_not_computable :
    ¬ ComputablePred fun q : Code × ℕ => (q.1.eval q.2).Dom := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine halting_undecidable ⟨fun p x => f (p, x), ?_, fun p x => ?_⟩
  · exact hf.comp (Computable.fst.pair Computable.snd)
  · have := congrFun hfe (p, x)
    simpa [eq_iff_iff] using this.symm

end CS

