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

open Nat.Partrec Nat.Partrec.Code

/-- The partial function computed by the program with (Gödel) index `n`. -/
noncomputable def phi (n : ℕ) : ℕ →. ℕ := Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n)

/-- Every partial recursive function is `phi n` for some index `n`. -/
theorem phi_surjective {g : ℕ →. ℕ} (hg : Nat.Partrec g) : ∃ n : ℕ, phi n = g := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hg
  exact ⟨Encodable.encode c, by simp [phi, hc]⟩

/-- Each index denotes a partial recursive function. -/
theorem partrec_phi (n : ℕ) : Nat.Partrec (phi n) :=
  Nat.Partrec.Code.exists_code.2 ⟨Denumerable.ofNat Nat.Partrec.Code n, rfl⟩

/--
**Kleene's recursion (fixed point) theorem.**
Every computable transformation `f` of program indices has a fixed point *up to
extensional behaviour*: there is an index `n` whose program computes exactly the
same partial function as the transformed program `f n`.
-/
theorem recursion_theorem {f : ℕ → ℕ} (hf : Computable f) : ∃ n : ℕ, phi (f n) = phi n := by
  have hF : Computable fun c : Code => (Denumerable.ofNat Nat.Partrec.Code (f (Encodable.encode c))) :=
    (Computable.ofNat Nat.Partrec.Code).comp (hf.comp Computable.encode)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hF
  refine ⟨Encodable.encode c, ?_⟩
  simpa [phi] using hc

/--
Version for computable transformations of programs (`Code`s): every computable
`f : Code → Code` has a program `c` such that `f c` and `c` compute the same
partial function.
-/
theorem recursion_theorem_code {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, Nat.Partrec.Code.eval (f c) = Nat.Partrec.Code.eval c :=
  Nat.Partrec.Code.fixed_point hf

/--
Kleene's second recursion theorem: for any partial recursive `f : ℕ → ℕ →. ℕ`
there is an index `n` with `phi n = f n`, i.e. a program that knows its own index.
-/
theorem recursion_theorem₂ {f : ℕ → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ n : ℕ, phi n = f n := by
  have hf' : Partrec₂ fun c : Code => f (Encodable.encode c) :=
    hf.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point₂ hf'
  exact ⟨Encodable.encode c, by simpa [phi] using hc⟩

end CS

