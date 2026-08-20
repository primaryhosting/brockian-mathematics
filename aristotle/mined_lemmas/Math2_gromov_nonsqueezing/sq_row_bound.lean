import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open Matrix

variable {n : ℕ}

/-- The standard symplectic form on `ℝ ^ (2 * n)`, with `ℝ ^ (2 * n)` modelled as functions
`(Fin n ⊕ Fin n) → ℝ`: the coordinates indexed by `Sum.inl i` are the positions `qᵢ` and the
coordinates indexed by `Sum.inr i` are the momenta `pᵢ`. -/

lemma sq_row_bound {i₀ : Fin n} {r R : ℝ}
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {b : (Fin n ⊕ Fin n) → ℝ}
    (h : (fun x => A *ᵥ x + b) '' ball r ⊆ cylinder i₀ R)
    {a : Fin n ⊕ Fin n} (ha : a = Sum.inl i₀ ∨ a = Sum.inr i₀) :
    r ^ 2 * (∑ k, A a k ^ 2) ≤ R ^ 2 := by
  set S : ℝ := ∑ k, A a k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases eq_or_lt_of_le hS0 with hzero | hpos
  · rw [← hzero, mul_zero]
    positivity
  · have hsq : 0 < Real.sqrt S := Real.sqrt_pos.2 hpos
    set c : ℝ := r / Real.sqrt S with hc
    have hcS : c ^ 2 * S = r ^ 2 := by
      rw [hc, div_pow, Real.sq_sqrt hS0]
      field_simp
    -- the two antipodal points of the ball in the direction of the row `A a`
    have main : ∀ t : ℝ, t ^ 2 = 1 → (t * c * S + b a) ^ 2 ≤ R ^ 2 := by
      intro t ht
      set x : (Fin n ⊕ Fin n) → ℝ := fun k => (t * c) * A a k with hx
      have hmem : x ∈ ball r := by
        show ∑ k, x k ^ 2 ≤ r ^ 2
        have hxs : ∑ k, x k ^ 2 = c ^ 2 * S := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hx]
          nlinarith [ht]
        rw [hxs, hcS]
      have hcyl := h ⟨x, hmem, rfl⟩
      have hval : (A *ᵥ x + b) a = t * c * S + b a := by
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct, hx, hS]
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
      have hcyl' : (A *ᵥ x + b) (Sum.inl i₀) ^ 2 + (A *ᵥ x + b) (Sum.inr i₀) ^ 2 ≤ R ^ 2 := hcyl
      have hkey : ((A *ᵥ x + b) a) ^ 2 ≤ R ^ 2 := by
        rcases ha with rfl | rfl
        · nlinarith [sq_nonneg ((A *ᵥ x + b) (Sum.inr i₀))]
        · nlinarith [sq_nonneg ((A *ᵥ x + b) (Sum.inl i₀))]
      rwa [hval] at hkey
    have h₁ := main 1 (by norm_num)
    have h₂ := main (-1) (by norm_num)
    have hkey : (c * S) ^ 2 ≤ R ^ 2 := by nlinarith [h₁, h₂]
    calc r ^ 2 * S = (c ^ 2 * S) * S := by rw [hcS]
      _ = (c * S) ^ 2 := by ring
      _ ≤ R ^ 2 := hkey

/-- **Gromov's nonsqueezing theorem for affine symplectic maps.**

If an affine symplectomorphism `x ↦ A *ᵥ x + b` of `ℝ ^ (2 * n)` (with `A` in the symplectic group,
so that the map preserves the standard symplectic form, cf. `Math2.omegaForm_mulVec`) maps the
closed ball of radius `r` into the symplectic cylinder of radius `R` over the `i₀`-th coordinate
symplectic plane, then `r ≤ R`. -/
