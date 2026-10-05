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

lemma card_le_of_pow_eq {F : Type*} [Field F] (V : Finset F) {m₁ m₂ : ℕ} (h : m₂ < m₁)
    (hV : ∀ v ∈ V, v ^ m₁ = v ^ m₂) : V.card ≤ m₁ := by
  classical
  set Q : F[X] := X ^ m₁ - X ^ m₂ with hQ
  have hcoeff : Q.coeff m₁ = 1 := by
    simp [hQ, coeff_X_pow, h.ne']
  have hQ0 : Q ≠ 0 := by
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hdeg : Q.natDegree ≤ m₁ := by
    rw [hQ]
    refine le_trans (natDegree_sub_le _ _) ?_
    simp only [natDegree_X_pow]
    omega
  have hsub : V.val ⊆ Q.roots := by
    intro v hv
    have hv' : v ∈ V := Finset.mem_val.mp hv
    rw [mem_roots hQ0]
    simp only [IsRoot.def, hQ, eval_sub, eval_pow, eval_X]
    rw [hV v hv', sub_self]
  exact le_trans (card_le_degree_of_subset_roots hsub) hdeg

/-- Two polynomials of degree at most `L` over `𝔽ₚ` agreeing at more than `L` points of the
algebraic closure are equal. -/
