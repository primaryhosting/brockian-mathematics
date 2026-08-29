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

open Nat.Partrec Nat.Partrec.Code Encodable

/-- **Kleene's recursion theorem** (Rogers' fixed point form).

Every computable transformation `f` of programs (codes for partial recursive functions
`ℕ →. ℕ`) has a fixed point *up to semantics*: there is a code `c` such that the program
`f c` computes exactly the same partial function as `c` does.

The proof is the classical diagonal argument: let `g x y = eval (ofNat Code x) x >>= fun b =>
eval (ofNat Code b) y`, a partial recursive function of `(x, y)`, and let `cg` be a code for it.
Currying `cg` at `x` gives a program which, on input `y`, runs program `x` on `x`, interprets the
result as a code, and runs it on `y`. Now let `F x = f (curry cg x)`, a computable function with
code `cF`. Then `c = curry cg (encode cF)` is a fixed point, since running `c` on `y` first
computes `cF` on `encode cF`, which returns the code `F (encode cF) = f c`, and then runs that
code on `y`. -/
theorem recursion_theorem {f : Nat.Partrec.Code → Nat.Partrec.Code} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, eval (f c) = eval c := by
  -- the universal diagonal function
  set g : ℕ → ℕ → Part ℕ :=
    fun x y => eval (Denumerable.ofNat Nat.Partrec.Code x) x >>= fun b =>
      eval (Denumerable.ofNat Nat.Partrec.Code b) y
    with hg
  have hgp : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.fst).bind
      (eval_part.comp ((Computable.ofNat _).comp Computable.snd)
        (Computable.snd.comp Computable.fst)).to₂
  obtain ⟨cg, eg⟩ := exists_code.1 hgp
  have eg' : ∀ a n : ℕ, eval cg (Nat.pair a n) = Part.map encode (g a n) := by
    simp [eg]
  -- the computable map `x ↦ f (curry cg x)`
  set F : ℕ → Nat.Partrec.Code := fun x => f (curry cg x) with hF
  have hFc : Computable F :=
    hf.comp (primrec₂_curry.comp (Primrec.const cg) Primrec.id).to_comp
  obtain ⟨cF, eF⟩ := exists_code.1 hFc
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by
    simp [eF]
  refine ⟨curry cg (encode cF), funext fun n => ?_⟩
  show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n
  simp [eval_curry, eg', eF', hg, hF, Part.map_id']

/-- **Kleene's second recursion theorem**: for every partial recursive `f : Code → ℕ →. ℕ`
(uniformly in the code argument) there is a program `c` that computes `f c`, i.e. a program
with access to its own source code. -/
theorem recursion_theorem₂ {f : Nat.Partrec.Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Nat.Partrec.Code, eval c = f c := by
  obtain ⟨cf, ef⟩ := exists_code.1 hf
  obtain ⟨c, hc⟩ :=
    recursion_theorem (f := fun c => curry cf (encode c))
      (primrec₂_curry.comp (Primrec.const cf) Primrec.encode).to_comp
  exact ⟨c, funext fun n => by simp [← hc, eval_curry, ef, Part.map_id']⟩

end CS

