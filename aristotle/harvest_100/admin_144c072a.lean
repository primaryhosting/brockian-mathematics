/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Kleene's recursion theorem: every computable transformation of programs has a fixed point.

Programs are the partial recursive codes `Nat.Partrec.Code`, indexed by natural numbers via
the `Denumerable` enumeration; `CS.phi n` is the partial function computed by the `n`-th
program. The main result `CS.recursion_theorem` states that for every total computable
`f : ℕ → ℕ` on program indices there is an index `n` with `phi (f n) = phi n`.

The proof is the usual diagonal argument via the s-m-n theorem (`Nat.Partrec.Code.curry`)
and the universal machine (`Nat.Partrec.Code.eval_part`).
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

open Nat.Partrec Nat.Partrec.Code Computable Partrec

/-- The partial function computed by the `n`-th program in the standard enumeration of
partial recursive codes. -/
noncomputable def phi (n : ℕ) : ℕ →. ℕ := eval (Denumerable.ofNat Code n)

/-- The "self-application" helper used in the diagonal argument: `diagEval x y` runs the
program with index `x` on input `x`, and then runs the program whose index is the result
on input `y`. -/
noncomputable def diagEval (x y : ℕ) : Part ℕ := (phi x x).bind fun b => phi b y

/-- `diagEval` is partial computable in both arguments. -/
theorem partrec₂_diagEval : Partrec₂ diagEval :=
  (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
    (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂

/-- **Kleene's recursion theorem** (Rogers' fixed point theorem), index form: every total
computable transformation `f` of program indices has a fixed point, i.e. there is an index
`n` such that the program `f n` computes exactly the same partial function as the program
`n`. -/
theorem recursion_theorem {f : ℕ → ℕ} (hf : Computable f) : ∃ n : ℕ, phi (f n) = phi n := by
  obtain ⟨cg, eg⟩ := exists_code.1 partrec₂_diagEval
  have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map Encodable.encode (diagEval a n) := by
    simp [eg]
  have hFc : Computable (fun x => f (Encodable.encode (curry cg x))) :=
    hf.comp (Primrec.encode.comp
      (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id)).to_comp
  obtain ⟨cF, eF⟩ := exists_code.1 hFc
  have eF' : eval cF (Encodable.encode cF)
      = Part.some (f (Encodable.encode (curry cg (Encodable.encode cF)))) := by
    simp [eF]
  refine ⟨Encodable.encode (curry cg (Encodable.encode cF)), funext fun y => ?_⟩
  show phi _ y = phi _ y
  simp only [phi, Denumerable.ofNat_encode, eval_curry, eg', diagEval, eF']
  simp [Part.map_id']

/-- **Kleene's recursion theorem**, code form: every computable transformation of programs
`f : Code → Code` has a fixed point up to extensional equality of computed partial
functions. -/
theorem recursion_theorem_code {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c := by
  obtain ⟨n, hn⟩ := recursion_theorem
    (Computable.encode.comp (hf.comp (Computable.ofNat Code)))
  exact ⟨Denumerable.ofNat Code n, by simpa [phi] using hn⟩

end CS

