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
noncomputable def diagFun (H : Nat.Partrec.Code → ℕ → Bool) : ℕ →. ℕ :=
  fun n => bif H (ofNat Nat.Partrec.Code n) n then Part.none else Part.some 0

/-- If `H` is computable (as a two-argument function), then the diagonal function
`diagFun H` is partial recursive. -/
theorem partrec_diagFun {H : Nat.Partrec.Code → ℕ → Bool} (hH : Computable₂ H) :
    Nat.Partrec (diagFun H) := by
  have hdiag : Computable fun n : ℕ => H (ofNat Nat.Partrec.Code n) n :=
    hH.comp (Computable.ofNat Nat.Partrec.Code) Computable.id
  have : Partrec (diagFun H) :=
    Partrec.cond hdiag Partrec.none (Computable.const (0 : ℕ)).partrec
  exact Partrec.nat_iff.mp this

/-- **The halting problem is undecidable.**

There is no total computable function `H` which, given a program `p` (an element of the
type `Nat.Partrec.Code` of codes for partial recursive functions) and an input `x`,
correctly decides whether `p` halts on `x`.

The proof is by diagonalization: from such an `H` one builds the partial recursive function
which, on input `n`, diverges exactly when `H` says the `n`-th program halts on `n`.
Taking a code `e` for this function and running it on its own index yields a contradiction. -/
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

