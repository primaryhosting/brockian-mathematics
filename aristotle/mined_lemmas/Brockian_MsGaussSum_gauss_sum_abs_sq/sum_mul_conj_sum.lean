import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma sum_mul_conj_sum (p : ℕ) [Fact p.Prime] :
    (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) *
        (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ))
      = ∑ m : ZMod p, (ZMod.stdAddChar (m ^ 2) : ℂ) * ∑ l : ZMod p, (ZMod.stdAddChar (2 * m * l) : ℂ) := by
  -- First, simplify the conjugate of the sum
  have h1 : (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) =
            ∑ k : ZMod p, (ZMod.stdAddChar (-(k ^ 2)) : ℂ) := by
    rw [map_sum]
    congr 1
    ext k
    exact conj_stdAddChar p (k ^ 2)
  rw [h1]
  -- Now we have a product of two sums, convert to double sum
  rw [Finset.sum_mul_sum]
  -- Combine the character values using the homomorphism property
  have h2 : ∀ i j : ZMod p, ZMod.stdAddChar (i ^ 2) * ZMod.stdAddChar (-j ^ 2) =
            ZMod.stdAddChar (i ^ 2 - j ^ 2) := by
    intro i j
    rw [sub_eq_add_neg]
    have h := (AddChar.toAddMonoidHom ZMod.stdAddChar).map_add (i ^ 2) (-j ^ 2)
    simp only [AddChar.toAddMonoidHom_apply] at h
    exact (congrArg Additive.toMul h).symm
  -- Rewrite using h2
  simp_rw [h2]
  -- Reindex: let m = x - x_1, so x = m + x_1
  -- x² - x_1² = (m + x_1)² - x_1² = m² + 2mx_1
  have reindex : ∀ x x_1 : ZMod p, x ^ 2 - x_1 ^ 2 = (x - x_1) ^ 2 + 2 * (x - x_1) * x_1 := by
    intro x x_1; ring
  simp_rw [reindex]
  -- Swap sums: ∑ x, ∑ x_1 → ∑ x_1, ∑ x
  rw [Finset.sum_comm]
  -- Now: ∑ x_1, ∑ x, stdAddChar((x - x_1)² + 2*(x - x_1)*x_1)
  -- Reindex inner sum: let m = x - x_1
  have reindex_inner : ∀ x_1 : ZMod p, ∑ x : ZMod p, ZMod.stdAddChar ((x - x_1) ^ 2 + 2 * (x - x_1) * x_1) =
      ∑ m : ZMod p, ZMod.stdAddChar (m ^ 2 + 2 * m * x_1) := by
    intro x_1
    rw [← Equiv.sum_comp (Equiv.addRight x_1)]
    simp [Equiv.addRight]
  simp_rw [reindex_inner]
  -- Now: ∑ x_1, ∑ m, stdAddChar(m² + 2*m*x_1)
  have h3 : ∀ m x_1 : ZMod p, ZMod.stdAddChar (m ^ 2 + 2 * m * x_1) =
            ZMod.stdAddChar (m ^ 2) * ZMod.stdAddChar (2 * m * x_1) := by
    intro m x_1
    have h := (AddChar.toAddMonoidHom ZMod.stdAddChar).map_add (m ^ 2) (2 * m * x_1)
    simp only [AddChar.toAddMonoidHom_apply] at h
    exact congrArg Additive.toMul h
  simp_rw [h3]
  -- Swap sums: now outer is m, inner is x_1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]

/-- The squared modulus of the quadratic Gauss sum equals `p`. -/
