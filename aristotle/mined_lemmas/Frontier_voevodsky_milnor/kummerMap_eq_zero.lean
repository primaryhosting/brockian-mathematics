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

lemma kummerMap_eq_zero (x : SquareClasses F) (hx : kummerMap h2 x = 0) : x = 0 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    have hchar : kummerChar h2 a = 0 := congrArg Subtype.val (kummerMap_mk h2 a ▸ hx)
    have hfix : ∀ σ : AbsGal F, σ (kummerRoot h2 a) = kummerRoot h2 a := by
      intro σ
      exact (kummerCharOf_eq_zero_iff _ σ).1 (congrFun hchar σ)
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (kummerRoot h2 a)).2 hfix
    have hy2 : algebraMap F (SeparableClosure F) (y ^ 2) = algebraMap F _ (a : F) := by
      rw [map_pow, hy, kummerRoot_sq]
    have hy2' : y ^ 2 = (a : F) :=
      (algebraMap F (SeparableClosure F)).injective hy2
    have hyne : y ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [← hy2', h]
      ring
    have : (Units.mk0 y hyne) ^ 2 = a := by
      ext
      simpa using hy2'
    show Additive.ofMul (QuotientGroup.mk a) = 0
    have hmk : (QuotientGroup.mk a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 y hyne, this⟩
    simp [hmk]

/-- **The Kummer map is injective**: a unit whose Kummer character is trivial is a square. -/
