import Mathlib.Computability.PartrecCode
/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Statement: Kleene's recursion theorem: every computable transformation of programs has a fixed point.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Computable Partrec Encodable

/-- The diagonal helper: `diag x y` runs the program coded by `x` on input `x`; if that
returns a code `b`, it then runs the program coded by `b` on input `y`. -/
noncomputable def diag (x y : ℕ) : Part ℕ :=
  eval (Denumerable.ofNat Code x) x >>= fun b => eval (Denumerable.ofNat Code b) y

theorem diag_partrec : Partrec₂ diag :=
  (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
    (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂

/-- **Kleene's recursion theorem** (Rogers' fixed point form): every computable
transformation `f` of programs has a fixed point, i.e. a code `c` such that `f c`
and `c` compute the same partial function. -/
theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c := by
  -- a code for the diagonal helper
  obtain ⟨cg, eg⟩ := exists_code.1 diag_partrec
  have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map encode (diag a n) := by simp [eg]
  -- `f` applied to the code obtained by fixing the first argument of `cg` to `x` is computable
  have hFcomp : Computable fun x => f (curry cg x) :=
    hf.comp (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
  obtain ⟨cF, eF⟩ := exists_code.1 hFcomp
  have eF' : eval cF (encode cF) = Part.some (encode (f (curry cg (encode cF)))) := by simp [eF]
  refine ⟨curry cg (encode cF), funext fun n => ?_⟩
  show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n
  simp [diag, eg', eF', Part.map_id']

/-- **Kleene's second recursion theorem**: for a partial computable `f` taking a program
and an input, there is a program `c` which computes `f c`, i.e. a program that has access
to its own code. -/
theorem recursion_theorem₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c := by
  obtain ⟨cf, ef⟩ := exists_code.1 hf
  obtain ⟨c, hc⟩ :=
    recursion_theorem
      (f := fun c => curry cf (encode c))
      (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp
  exact ⟨c, funext fun n => by simp [← hc, ef, Part.map_id']⟩

end CS

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

