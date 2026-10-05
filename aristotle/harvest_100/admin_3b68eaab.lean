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
theorem halting_undecidable :
    ¬ ∃ H : Code → ℕ → Bool,
        Computable₂ H ∧ ∀ p x, H p x = true ↔ (p.eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  -- The diagonal program: on input `n`, diverge iff the `n`-th program halts on `n`.
  set D : ℕ →. ℕ :=
    fun n => bif H (Denumerable.ofNat Code n) n then Part.none else Part.some 0 with hDdef
  have hcomp : Computable fun n : ℕ => H (Denumerable.ofNat Code n) n :=
    hH.comp (Computable.ofNat _) Computable.id
  have hD : Nat.Partrec D :=
    Partrec.nat_iff.mp (Partrec.cond hcomp Partrec.none (Partrec.const' _))
  obtain ⟨c, hc⟩ := exists_code.mp hD
  -- Run the diagonal program on (a code for) itself.
  set n := Encodable.encode c
  have hdec : Denumerable.ofNat Code n = c := Denumerable.ofNat_encode c
  have hval : c.eval n = bif H c n then Part.none else Part.some 0 := by
    simp only [hc, hDdef, hdec]
  rcases hb : H c n with _ | _
  · -- `H` says it does not halt, but it returns `0`.
    have : (c.eval n).Dom := by rw [hval, hb]; trivial
    rw [← hspec c n, hb] at this
    exact Bool.noConfusion this
  · -- `H` says it halts, but it diverges.
    have hdom : (c.eval n).Dom := (hspec c n).mp hb
    rw [hval, hb] at hdom
    exact hdom

/-- Restatement of the undecidability of the halting problem: the halting set
`{(p, x) | p halts on x}` is not a computable predicate. -/
theorem halting_set_not_computable :
    ¬ ComputablePred fun q : Code × ℕ => (q.1.eval q.2).Dom := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine halting_undecidable ⟨fun p x => f (p, x), ?_, fun p x => ?_⟩
  · exact hf.comp (Computable.fst.pair Computable.snd)
  · have := congrFun hfe (p, x)
    simpa [eq_iff_iff] using this.symm

end CS

