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

import RequestProject.AKS.Defs

/-!
# Introspective exponents

Fix a prime `p` and let `F = AlgebraicClosure (ZMod p)`.  A natural number `m` is
*introspective* for a polynomial `f ∈ 𝔽ₚ[X]` (relative to `r`) if `f(z)^m = f(z^m)` for every
`r`-th root of unity `z ∈ F`.  This is the key notion in the AKS correctness proof.
-/

open Polynomial

namespace CS
namespace AKS

/-- The algebraic closure of `𝔽ₚ`, the field in which the AKS argument takes place. -/
abbrev AC (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

variable {p : ℕ} [Fact p.Prime]

/-- `m` is introspective for `f`: `f(z)^m = f(z^m)` for all `r`-th roots of unity `z`. -/

lemma prod_X_add_C_inj {L : ℕ} (hLp : L < p) {S T : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 L) (hT : T ⊆ Finset.Icc 1 L)
    (h : (∏ a ∈ S, (X + C (a : ZMod p))) = ∏ a ∈ T, (X + C (a : ZMod p))) : S = T := by
  classical
  have hcast : ∀ x ∈ Finset.Icc 1 L, ∀ y ∈ Finset.Icc 1 L,
      (x : ZMod p) = (y : ZMod p) → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_Icc] at hx hy
    have := (ZMod.natCast_eq_natCast_iff x y p).mp hxy
    have hx' : x < p := by omega
    have hy' : y < p := by omega
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
  have key : ∀ (U : Finset ℕ), U ⊆ Finset.Icc 1 L → ∀ a ∈ Finset.Icc 1 L,
      ((∏ b ∈ U, (X + C (b : ZMod p))).eval (-(a : ZMod p)) = 0 ↔ a ∈ U) := by
    intro U hU a ha
    rw [eval_prod]
    rw [Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨b, hb, hb0⟩
      simp only [eval_add, eval_X, eval_C] at hb0
      have : (b : ZMod p) = (a : ZMod p) := by linear_combination hb0
      rwa [hcast b (hU hb) a ha this] at hb
    · intro haU
      exact ⟨a, haU, by simp⟩
  ext a
  by_cases ha : a ∈ Finset.Icc 1 L
  · rw [← key S hS a ha, ← key T hT a ha, h]
  · constructor
    · intro haS; exact absurd (hS haS) ha
    · intro haT; exact absurd (hT haT) ha

/-- The AKS polynomial congruence modulo `n` gives introspectiveness of `n`
for `X + a` over any prime factor `p` of `n`. -/
