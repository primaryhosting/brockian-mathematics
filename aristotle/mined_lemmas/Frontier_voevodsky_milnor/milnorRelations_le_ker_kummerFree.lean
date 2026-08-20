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

lemma milnorRelations_le_ker_kummerFree (hF : (2 : F) ≠ 0) :
    Submodule.span (ZMod 2) (milnorRelations F 1) ≤ LinearMap.ker (kummerFree hF) := by
  rw [Submodule.span_le]
  rintro x (⟨i, a, b, v, rfl⟩ | ⟨i, j, v, hij, -, -⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, kummerFree_single,
      Function.update_self]
    ext σ
    have h := congrFun (kummerChar_mul hF a b) σ
    simp only [Submodule.coe_sub, Pi.sub_apply, Pi.add_apply, ZeroMemClass.coe_zero,
      Pi.zero_apply] at h ⊢
    rw [h]
    ring
  · exact absurd (Subsingleton.elim i j) hij

/-- The degree-one norm residue map `K^M_1(F)/2 → Homcont(Gal(F^sep/F), ℤ/2)`. -/
