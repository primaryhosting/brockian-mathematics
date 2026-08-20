import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

lemma exists_sq (hchar : ringChar F ≠ 2) (a : Fˣ) : ∃ b : Fˣ, b * b = a := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ringChar_ne_two F hchar
  have hsep : (Polynomial.X ^ 2 - Polynomial.C (a : F)).Separable :=
    Polynomial.separable_X_pow_sub_C (n := 2) (a : F) (by simpa using h2) a.ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (a : F)).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]
    simp
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep
  have hx2 : x ^ 2 = (a : F) := by
    have hr := hx
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hr
    exact hr
  have hxne : x ≠ 0 := by
    intro h
    apply a.ne_zero
    rw [← hx2, h]; ring
  refine ⟨Units.mk0 x hxne, ?_⟩
  ext
  simpa [pow_two] using hx2

/-- The absolute Galois group of a separably closed field is trivial. -/
instance absGal_subsingleton : Subsingleton (AbsGal F) := by
  have hs : Function.Surjective (algebraMap F (SeparableClosure F)) :=
    IsSepClosed.algebraMap_surjective F (SeparableClosure F)
  refine ⟨fun σ τ => ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hs x
  simp

/-- Mod-2 Milnor K-theory of a separably closed field of characteristic `≠ 2` vanishes in
positive degrees. -/
