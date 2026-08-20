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

Programs are modelled by `Nat.Partrec.Code`, the standard Mathlib type of codes for partial
recursive functions, whose semantics is `Nat.Partrec.Code.eval : Code → ℕ →. ℕ`.

The main theorem `CS.recursion_theorem` is given a self-contained proof from the universality
of `eval` (`Nat.Partrec.Code.eval_part`), the fact that partial recursive functions have codes
(`Nat.Partrec.Code.exists_code`), and the s-m-n theorem in the form
`Nat.Partrec.Code.primrec₂_curry` / `Nat.Partrec.Code.eval_curry`.
Mathlib also states this result directly as `Nat.Partrec.Code.fixed_point`
(and `Nat.Partrec.Code.fixed_point₂`); see `CS.recursion_theorem_via_mathlib` below.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/-- **Kleene's recursion theorem** (Rogers' fixed-point form): every computable
transformation `f` of programs has a fixed point up to semantics, i.e. there is a code `c`
such that the program `f c` computes exactly the same partial function as `c`.

Proof (Kleene's diagonal argument): let `g x y` run the program coded by `x` on input `x`,
read the result as a code, and run that code on `y`; `g` is partial recursive, say with code
`cg`. By the s-m-n theorem `n ↦ f (curry cg n)` is computable, so it has a code `cF`, and
`c := curry cg (encode cF)` is a fixed point: on input `n`, `c` first computes
`encode (f (curry cg (encode cF))) = encode (f c)` and then runs it on `n`. -/

theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c := by
  -- `g x y`: run the program coded by `x` on input `x`, then read the output as a code and
  -- run it on `y`.  This is partial recursive since `eval` is.
  set g : ℕ → ℕ → Part ℕ :=
    fun x y => eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y with hg
  have hpg : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.fst).bind
      (eval_part.comp ((Computable.ofNat _).comp Computable.snd)
        (Computable.snd.comp Computable.fst)).to₂
  obtain ⟨cg, eg⟩ := exists_code.1 hpg
  have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map encode (g a n) := by simp [eg, hg]
  -- By the s-m-n theorem, `F n = f (curry cg n)` is computable, so it has a code `cF`.
  set F : ℕ → Code := fun n => f (curry cg n) with hF0
  have hFc : Computable F :=
    hf.comp (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
  obtain ⟨cF, eF⟩ := exists_code.1 hFc
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
  -- The diagonal code `curry cg (encode cF)` is a fixed point of `f`.
  refine ⟨curry cg (encode cF), funext fun n => ?_⟩
  show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n
  simp [hF0, hg, eg', eF', Part.map_id', eval_curry]

/-- The same statement as `CS.recursion_theorem`, closed by the existing Mathlib lemma
`Nat.Partrec.Code.fixed_point`. -/
