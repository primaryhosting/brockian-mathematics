/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma degD_nonneg_of_mem_LSpace {D : P →₀ ℤ} {x : F} (hx : x ≠ 0) (hxD : x ∈ C.LSpace D) :
    0 ≤ C.degD D := by
  classical
  obtain ⟨S₀, hS₀⟩ := C.ord_support x hx
  set S : Finset P := S₀ ∪ D.support with hSdef
  have hsupp : ∀ p ∉ S, C.ord p x = (0 : Zt) := by
    intro p hp
    exact hS₀ p fun h => hp (Finset.mem_union_left _ h)
  have h0 := C.degree_principal x hx S hsupp
  have hle : ∀ p ∈ S, (C.deg p : ℤ) * (-(D p)) ≤ (C.deg p : ℤ) * C.ordZ p x := by
    intro p _
    have h := hxD p
    rw [C.ord_eq_ordZ hx] at h
    have : -(D p) ≤ C.ordZ p x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum : ∑ p ∈ S, (C.deg p : ℤ) * (-(D p)) ≤ ∑ p ∈ S, (C.deg p : ℤ) * C.ordZ p x :=
    Finset.sum_le_sum hle
  have hdeg : C.degD D = ∑ p ∈ S, D p * (C.deg p : ℤ) :=
    C.degD_eq_sum (by intro p hp; exact Finset.mem_union_right _ hp)
  have h0' : ∑ p ∈ S, (C.deg p : ℤ) * C.ordZ p x = 0 := by
    rw [← h0]; rfl
  have : ∑ p ∈ S, (C.deg p : ℤ) * (-(D p)) = - C.degD D := by
    rw [hdeg, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [this, h0'] at hsum
  linarith

