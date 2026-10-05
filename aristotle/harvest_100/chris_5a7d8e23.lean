import Mathlib

/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the header module docstring
is placed immediately after the import.)
-/

/-!
Kleene's recursion theorem (Rogers' fixed-point form): every computable transformation of
programs has a fixed point, i.e. a program whose behaviour is unchanged by the transformation.

Programs are the partial recursive codes `Nat.Partrec.Code`, and `Nat.Partrec.Code.eval` gives
the partial function computed by a code.  Program *indices* are natural numbers, related to codes
by the denumerable structure `Denumerable.ofNat Code` / `Encodable.encode`.

The main theorem `CS.recursion_theorem` is stated at the level of indices: for every computable
`f : ℕ → ℕ` there is an index `e` with the programs `f e` and `e` computing the same partial
function.  It is proved directly by the diagonalisation argument (self-application composed with
the s-m-n theorem `Nat.Partrec.Code.curry`), not by invoking Mathlib's `fixed_point`.

Two standard consequences are derived: the code-level fixed-point statement and Kleene's second
recursion theorem.
-/

open Nat.Partrec Nat.Partrec.Code Computable Partrec Denumerable Encodable

namespace CS

/-- **Kleene's recursion theorem** (Rogers' fixed-point form), index version:
every computable transformation `f : ℕ → ℕ` of program indices has a fixed point, i.e. an
index `e` such that the programs with indices `f e` and `e` compute the same partial function. -/
theorem recursion_theorem {f : ℕ → ℕ} (hf : Computable f) :
    ∃ e : ℕ, eval (ofNat Code (f e)) = eval (ofNat Code e) := by
  -- The diagonal function `g x y = φ_{φ_x(x)}(y)` is partial recursive.
  have hgp : Partrec₂ (fun x y : ℕ => eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y) :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  obtain ⟨cg, eg⟩ := exists_code.1 hgp
  have eg' : ∀ a n : ℕ, eval cg (Nat.pair a n)
      = Part.map encode (eval (ofNat Code a) a >>= fun b => eval (ofNat Code b) n) := by
    simp [eg]
  -- `F x = f (index of the program `y ↦ g x y`)` is computable, by s-m-n.
  have hFc : Computable (fun x : ℕ => f (encode (curry cg x))) :=
    hf.comp ((Primrec.encode.comp
      (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id)).to_comp)
  obtain ⟨cF, eF⟩ := exists_code.1 hFc
  have eF' : eval cF (encode cF) = Part.some (f (encode (curry cg (encode cF)))) := by simp [eF]
  -- Feeding the code of `F` to the diagonal gives the fixed point.
  refine ⟨encode (curry cg (encode cF)), funext fun n => ?_⟩
  have hcurry : eval (ofNat Code (encode (curry cg (encode cF)))) n
      = eval cg (Nat.pair (encode cF) n) := by
    simp [eval_curry]
  rw [hcurry, eg']
  simp [eF', Part.map_id']

/-- **Rogers' fixed-point theorem**, code version: every computable transformation of programs
`f : Code → Code` has a fixed point `c`, i.e. `f c` and `c` compute the same partial function. -/
theorem recursion_theorem_code {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c := by
  have hf' : Computable (fun e : ℕ => encode (f (ofNat Code e))) :=
    Primrec.encode.to_comp.comp (hf.comp (Computable.ofNat _))
  obtain ⟨e, he⟩ := recursion_theorem hf'
  exact ⟨ofNat Code e, by simpa using he⟩

/-- **Kleene's second recursion theorem**: for a partial recursive `f : Code → ℕ →. ℕ` there is a
program `c` that computes `f c`, i.e. a program with access to its own code. -/
theorem kleene_second_recursion_theorem {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c := by
  obtain ⟨cf, ef⟩ := exists_code.1 hf
  obtain ⟨c, hc⟩ := recursion_theorem_code
    (f := fun c => curry cf (encode c))
    (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp
  exact ⟨c, funext fun n => by simp [← hc, eval_curry, ef, Part.map_id']⟩

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

