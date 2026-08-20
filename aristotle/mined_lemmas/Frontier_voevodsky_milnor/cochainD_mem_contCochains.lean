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

lemma cochainD_mem_contCochains {n : ℕ} {f : (Fin n → G) → ZMod 2}
    (hf : f ∈ contCochains G n) : cochainD G n f ∈ contCochains G (n + 1) := by
  rw [mem_contCochains] at hf ⊢
  have hcont : Continuous fun g : Fin (n + 1) → G => f (fun i => g i.succ) :=
    hf.comp (continuous_pi fun i => continuous_apply _)
  have hsum : ∀ j : Fin (n + 1),
      Continuous fun g : Fin (n + 1) → G => f (Fin.contractNth j (· * ·) g) := by
    intro j
    refine hf.comp (continuous_pi fun i => ?_)
    unfold Fin.contractNth
    split_ifs
    · exact continuous_apply (A := fun _ : Fin (n + 1) => G) i.castSucc
    · exact (continuous_apply (A := fun _ : Fin (n + 1) => G) i.castSucc).mul
        (continuous_apply (A := fun _ : Fin (n + 1) => G) i.succ)
    · exact continuous_apply (A := fun _ : Fin (n + 1) => G) i.succ
  have heq : (cochainD G n f) = fun g => f (fun i => g i.succ) +
      ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
    funext g; exact cochainD_apply G n f g
  rw [heq]
  exact hcont.add (continuous_finset_sum _ fun j _ => hsum j)

/-- Continuous cocycles: continuous cochains killed by the differential. -/
