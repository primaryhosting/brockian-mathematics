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

import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

`K^M_n(F)/2` is the abelian group (a `ZMod 2`-vector space) presented by generators the
symbols `{a₁, …, aₙ}` with `aᵢ ∈ Fˣ`, subject to
* multilinearity `{…, a·b, …} = {…, a, …} + {…, b, …}`, and
* the Steinberg relation `{…, a, …, 1 - a, …} = 0`.

Since the coefficients are taken in `ZMod 2` this is exactly Milnor K-theory modulo `2`.

## Main definitions

* `Frontier.milnorRelations F n` : the set of defining relations.
* `Frontier.KMilnorMod2 F n` : the group `K^M_n(F)/2`.
* `Frontier.symbol F v` : the symbol `{v 0, …, v (n-1)}`.

## Main results

* `Frontier.kMilnorMod2ZeroEquiv` : `K^M_0(F)/2 ≃ ℤ/2`.
* `Frontier.exists_symbol_eq_one` : in degree one, every element is a single symbol.
-/

namespace Frontier

variable (F : Type) [Field F]

/-- The defining relations of `K^M_n(F)/2`: multilinearity in each slot and the Steinberg
relation `{…, a, …, 1 - a, …} = 0`. -/

lemma kummerChar_add (hF : (2 : F) ≠ 0) (a : Fˣ) (σ τ : GalGroup F) :
    kummerChar a (σ * τ) = kummerChar a σ + kummerChar a τ := by
  have hmul : (σ * τ) (sqrtIn a) = σ (τ (sqrtIn a)) := rfl
  rcases sqrtIn_conj hF a σ with hs | hs <;> rcases sqrtIn_conj hF a τ with ht | ht
  · rw [kummerChar_of_fix (by rw [hmul, ht, hs]), kummerChar_of_fix hs, kummerChar_of_fix ht]
    simp
  · rw [kummerChar_of_neg hF (by rw [hmul, ht, map_neg, hs]), kummerChar_of_fix hs,
      kummerChar_of_neg hF ht]
    simp
  · rw [kummerChar_of_neg hF (by rw [hmul, ht, hs]), kummerChar_of_neg hF hs,
      kummerChar_of_fix ht]
    simp
  · rw [kummerChar_of_fix (by rw [hmul, ht, map_neg, hs, neg_neg]), kummerChar_of_neg hF hs,
      kummerChar_of_neg hF ht]
    decide

/-- A homomorphism to `ZMod 2` with open kernel is continuous. -/
