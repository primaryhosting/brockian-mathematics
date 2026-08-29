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
noncomputable def diag (H : Code → ℕ → Bool) : ℕ →. ℕ :=
  fun n => bif H (ofNat Code n) n then Part.none else Part.some 0

/-- If `H` is computable in both arguments, then the diagonal function is partial
recursive. -/
theorem diag_partrec {H : Code → ℕ → Bool} (hH : Computable₂ H) :
    Nat.Partrec (diag H) := by
  have hb : Computable fun n : ℕ => H (ofNat Code n) n := hH.comp
    (Computable.ofNat _) Computable.id
  have : Partrec (diag H) :=
    Partrec.cond hb Partrec.none (Computable.const (0 : ℕ)).partrec
  simpa [Partrec] using this

/-- The diagonal function halts on `n` exactly when `H` says the `n`-th program
does not halt on `n`. -/
theorem diag_dom_iff (H : Code → ℕ → Bool) (n : ℕ) :
    (diag H n).Dom ↔ H (ofNat Code n) n = false := by
  unfold diag
  cases h : H (ofNat Code n) n <;> simp

/-- **The halting problem is undecidable.**
There is no total computable function `H` which, given (a code for) a program `p`
and an input `x`, decides whether `p` halts on `x`.  The proof is by
diagonalization: from such an `H` one builds a program that halts on its own code
exactly when `H` says it does not. -/
theorem halting_undecidable :
    ¬ ∃ H : Code → ℕ → Bool,
        Computable₂ H ∧ ∀ (p : Code) (x : ℕ), H p x = true ↔ (p.eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  -- The diagonal function is partial recursive, hence has a code `c`.
  obtain ⟨c, hc⟩ := Code.exists_code.mp (diag_partrec hH)
  -- Run `c` on its own index.
  set n := encode c with hn
  have hofNat : ofNat Code n = c := by
    simp [hn, Denumerable.ofNat_encode]
  have h1 : H c n = true ↔ (c.eval n).Dom := hspec c n
  have h2 : (c.eval n).Dom ↔ H c n = false := by
    rw [hc, diag_dom_iff, hofNat]
  have h3 : H c n = true ↔ H c n = false := h1.trans h2
  cases hb : H c n with
  | false => simp [hb] at h3
  | true => simp [hb] at h3

/-- Index-based restatement: there is no total computable `H : ℕ → ℕ → Bool` such
that `H e x = true` exactly when the program with index `e` halts on input `x`. -/
theorem halting_undecidable_index :
    ¬ ∃ H : ℕ → ℕ → Bool,
        Computable₂ H ∧ ∀ (e x : ℕ), H e x = true ↔ ((ofNat Code e).eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine halting_undecidable ⟨fun p x => H (encode p) x, ?_, ?_⟩
  · exact hH.comp (Computable.encode.comp Computable.fst) Computable.snd
  · intro p x
    simpa [Denumerable.ofNat_encode] using hspec (encode p) x

end CS

