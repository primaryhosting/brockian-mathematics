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

open Encodable Nat.Partrec Nat.Partrec.Code

/-- The diagonal helper used in Kleene's argument: on input `(x, y)` it runs the program
coded by `x` on input `x`, and then runs the program whose code is the resulting output
on input `y`.  This is a partial recursive function of two arguments. -/
noncomputable def diagAux (x y : ℕ) : Part ℕ :=
  eval (Denumerable.ofNat Code x) x >>= fun b => eval (Denumerable.ofNat Code b) y

theorem partrec₂_diagAux : Partrec₂ diagAux :=
  (eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.fst).bind
    (eval_part.comp ((Computable.ofNat _).comp Computable.snd)
      (Computable.snd.comp Computable.fst)).to₂

/-- **Kleene's recursion theorem** (Rogers' fixed point form): every computable
transformation `f` of programs has a fixed point, i.e. a program `c` such that `c` and
`f c` compute exactly the same partial function. -/
theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c := by
  -- A code `cg` for the diagonal helper.
  obtain ⟨cg, hcg⟩ := exists_code.1 partrec₂_diagAux
  have hcg' : ∀ a n : ℕ, eval cg (Nat.pair a n) = Part.map Encodable.encode (diagAux a n) := by
    simp [hcg]
  -- The computable map `x ↦ f (curry cg x)`, and a code `cF` for it.
  have hF : Computable (fun x : ℕ => Encodable.encode (f (curry cg x))) :=
    (Computable.encode).comp
      (hf.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const cg) Primrec.id).to_comp)
  obtain ⟨cF, hcF⟩ := exists_code.1 hF
  have hcF' : eval cF (Encodable.encode cF)
      = Part.some (Encodable.encode (f (curry cg (Encodable.encode cF)))) := by
    simp [hcF]
  -- The fixed point is `curry cg ⌜cF⌝`.
  refine ⟨curry cg (Encodable.encode cF), funext fun n => ?_⟩
  have h1 : eval (curry cg (Encodable.encode cF)) n
      = Part.map Encodable.encode (diagAux (Encodable.encode cF) n) := by
    simpa using hcg' (Encodable.encode cF) n
  have h2 : diagAux (Encodable.encode cF) n
      = eval (f (curry cg (Encodable.encode cF))) n := by
    simp [diagAux, hcF']
  rw [h1, h2, Part.map_id']
  intro a
  rfl

/-- **Kleene's second recursion theorem**: for any partial computable `f : Code → ℕ →. ℕ`
there is a program `c` computing `f c`, i.e. a program that has access to its own code. -/
theorem recursion_theorem₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c := by
  obtain ⟨cf, hcf⟩ := exists_code.1 hf
  obtain ⟨c, hc⟩ := recursion_theorem
    (f := fun c : Code => curry cf (Encodable.encode c))
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const cf) Primrec.encode).to_comp
  refine ⟨c, funext fun n => ?_⟩
  have : eval (curry cf (Encodable.encode c)) n = Part.map Encodable.encode (f c n) := by
    simpa using congrFun hcf (Nat.pair (Encodable.encode c) n)
  rw [← hc, this, Part.map_id']
  intro a
  rfl

/-- Index form of the recursion theorem: every total computable function on program codes
has a fixed point up to extensional equality of the programs coded. -/
theorem recursion_theorem_index {f : ℕ → ℕ} (hf : Computable f) :
    ∃ n : ℕ, eval (Denumerable.ofNat Code (f n)) = eval (Denumerable.ofNat Code n) := by
  obtain ⟨c, hc⟩ := recursion_theorem
    (f := fun c : Code => Denumerable.ofNat Code (f (Encodable.encode c)))
    ((Computable.ofNat Code).comp (hf.comp Computable.encode))
  exact ⟨Encodable.encode c, by simpa using hc⟩

end CS

