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

lemma kummerCharOf_eq_one_iff {s : SeparableClosure F} (h2 : (2 : F) ≠ 0) (hs0 : s ≠ 0)
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a) (σ : AbsGal F) :
    kummerCharOf s σ = 1 ↔ σ s = -s := by
  constructor
  · intro h
    rcases sigma_eq_or_eq_neg hs σ with hσ | hσ
    · rw [(kummerCharOf_eq_zero_iff s σ).2 hσ] at h
      exact absurd h (by decide)
    · exact hσ
  · intro hσ
    unfold kummerCharOf
    rw [if_neg]
    rw [hσ]
    exact fun h => (ne_neg_self h2 hs0) h.symm

