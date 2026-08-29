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

