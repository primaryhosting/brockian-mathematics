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

theorem halting_undecidable_nat :
    ¬ ∃ H : ℕ → ℕ → ℕ,
        Computable₂ H ∧ ∀ (p x : ℕ), H p x = 1 ↔ (eval (ofNat Nat.Partrec.Code p) x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine halting_undecidable ⟨fun p x => decide (H (encode p) x = 1), ?_, ?_⟩
  · have h1 : Computable₂ fun (p : Nat.Partrec.Code) (x : ℕ) => H (encode p) x :=
      hH.comp (Computable.encode.comp Computable.fst) Computable.snd
    obtain ⟨inst, heq⟩ := Primrec.eq (α := ℕ)
    have heq' : Computable fun m : ℕ => decide (m = 1) := by
      have h2 := heq.comp (Primrec.id.pair (Primrec.const (1 : ℕ)))
      exact (h2.of_eq (fun m => by simp)).to_comp
    exact heq'.comp₂ h1
  · intro p x
    simpa [Denumerable.ofNat_encode] using hspec (encode p) x

end CS

