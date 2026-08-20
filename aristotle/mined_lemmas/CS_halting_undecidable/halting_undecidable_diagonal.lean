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

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/--
**The halting problem is undecidable.**

There is no total computable function `H : Code → ℕ → Bool` such that for every program
(code) `c` and every input `x`, `H c x = true` exactly when the program `c` halts on input `x`
(i.e. the partial function `eval c` is defined at `x`).

The proof reduces to Mathlib's `ComputablePred.halting_problem`, which states that for each
fixed input `n` the predicate `fun c => (eval c n).Dom` is not computable; that result is in
turn a consequence of Rice's theorem, whose proof is the usual diagonalization argument.
A direct diagonalization proof of the same statement is given below as
`CS.halting_undecidable_diagonal`.
-/

theorem halting_undecidable_diagonal :
    ¬ ∃ H : Code → ℕ → Bool,
        Computable₂ H ∧ ∀ c x, H c x = true ↔ (eval c x).Dom := by
  rintro ⟨H, hHc, hH⟩
  -- The diagonal partial function: diverge iff `H` says the `n`-th program halts on `n`.
  set g : ℕ →. ℕ := fun n => bif H (ofNat Code n) n then Part.none else Part.some 0 with hg
  have hgpart : Nat.Partrec g :=
    Partrec.nat_iff.1 <|
      Partrec.cond (hHc.comp (Computable.ofNat Code) Computable.id)
        Partrec.none (Computable.const 0).partrec
  obtain ⟨e, he⟩ := exists_code.1 hgpart
  have hgd : (g (encode e)).Dom ↔ (eval e (encode e)).Dom := by rw [he]
  have key : (eval e (encode e)).Dom ↔ ¬ (eval e (encode e)).Dom := by
    constructor
    · intro hd
      have h1 : H e (encode e) = true := (hH e (encode e)).2 hd
      have h2 := hgd.2 hd
      rw [hg] at h2
      simp [h1] at h2
    · intro hnd
      have h1 : H e (encode e) = false := by
        cases h : H e (encode e) with
        | false => rfl
        | true => exact absurd ((hH e (encode e)).1 h) hnd
      have hdom : (g (encode e)).Dom := by rw [hg]; simp [h1]
      exact hgd.1 hdom
  rcases Classical.em ((eval e (encode e)).Dom) with h | h
  · exact absurd h (key.1 h)
  · exact absurd (key.2 h) h

end CS

