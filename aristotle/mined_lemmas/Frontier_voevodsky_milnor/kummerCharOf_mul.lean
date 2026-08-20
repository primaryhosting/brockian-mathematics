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

lemma kummerCharOf_mul {s t : SeparableClosure F} (h2 : (2 : F) ≠ 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a)
    (ht : ∃ a : F, t ^ 2 = algebraMap F (SeparableClosure F) a) :
    kummerCharOf (s * t) = kummerCharOf s + kummerCharOf t := by
  have hst : ∃ a : F, (s * t) ^ 2 = algebraMap F (SeparableClosure F) a := by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a * b, by rw [mul_pow, ha, hb, map_mul]⟩
  have hst0 : s * t ≠ 0 := mul_ne_zero hs0 ht0
  funext σ
  rcases sigma_eq_or_eq_neg hs σ with hσs | hσs <;> rcases sigma_eq_or_eq_neg ht σ with hσt | hσt
  · have h : σ (s * t) = s * t := by rw [map_mul, hσs, hσt]
    rw [Pi.add_apply, (kummerCharOf_eq_zero_iff _ σ).2 h, (kummerCharOf_eq_zero_iff _ σ).2 hσs,
      (kummerCharOf_eq_zero_iff _ σ).2 hσt]
    decide
  · have h : σ (s * t) = -(s * t) := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_one_iff h2 hst0 hst σ).2 h,
      (kummerCharOf_eq_zero_iff _ σ).2 hσs, (kummerCharOf_eq_one_iff h2 ht0 ht σ).2 hσt]
    decide
  · have h : σ (s * t) = -(s * t) := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_one_iff h2 hst0 hst σ).2 h,
      (kummerCharOf_eq_one_iff h2 hs0 hs σ).2 hσs, (kummerCharOf_eq_zero_iff _ σ).2 hσt]
    decide
  · have h : σ (s * t) = s * t := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_zero_iff _ σ).2 h,
      (kummerCharOf_eq_one_iff h2 hs0 hs σ).2 hσs, (kummerCharOf_eq_one_iff h2 ht0 ht σ).2 hσt]
    decide

