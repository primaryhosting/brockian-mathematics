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

lemma galoisCohomologyMod2_succ_subsingleton (n : ℕ) :
    Subsingleton (GaloisCohomologyMod2 F (n + 1)) := by
  rw [Submodule.Quotient.subsingleton_iff]
  refine eq_top_iff.2 fun x _ => ?_
  show (x : (Fin (n + 1) → AbsGal F) → ZMod 2) ∈ contCoboundaries F (n + 1)
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n` is even, so `n + 1` is odd: the differential out of degree `n + 1` is injective.
    have hker : dd (AbsGal F) (n + 1) (x : (Fin (n + 1) → AbsGal F) → ZMod 2) = 0 := x.2.2
    have hcast : ((n + 1 : ℕ) : ZMod 2) = 1 := by
      rw [hk, Nat.cast_add, natCast_add_self_zmod_two, Nat.cast_one, zero_add]
    have hx0 : (x : (Fin (n + 1) → AbsGal F) → ZMod 2) = 0 := by
      funext g
      have hg := congrFun hker (fun _ => 1)
      rw [dd_subsingleton (AbsGal F) (n + 1) _ _ g, hcast, one_mul] at hg
      simpa using hg
    rw [hx0]
    exact Submodule.zero_mem _
  · -- `n` is odd: the differential into degree `n + 1` is surjective.
    have hcast : ((n : ℕ) : ZMod 2) = 1 := by
      rw [hk, show 2 * k + 1 = (k + k) + 1 by ring, Nat.cast_add, natCast_add_self_zmod_two,
        Nat.cast_one, zero_add]
    refine ⟨fun _ => (x : (Fin (n + 1) → AbsGal F) → ZMod 2) (fun _ => 1), ?_, ?_⟩
    · rw [contCochains_eq_top_of_isSepClosed]; trivial
    · funext g
      rw [dd_subsingleton (AbsGal F) n _ _ (fun _ => 1), hcast, one_mul]
      exact congrArg (x : (Fin (n + 1) → AbsGal F) → ZMod 2) (Subsingleton.elim _ _)

/-- **The Milnor conjecture holds for separably closed fields of characteristic `≠ 2`**, in every
degree: both sides vanish in positive degrees, and both are `ℤ/2` in degree `0`. -/
