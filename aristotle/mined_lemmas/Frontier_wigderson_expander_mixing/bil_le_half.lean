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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma bil_le_half (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hlam : ∀ f : V → ℝ, ∑ v, f v = 0 → |bil A f f| ≤ lam * ∑ v, (f v) ^ 2)
    (f g : V → ℝ) (hf : ∑ v, f v = 0) (hg : ∑ v, g v = 0) :
    |bil A f g| ≤ lam * ((∑ v, (f v) ^ 2) + (∑ v, (g v) ^ 2)) / 2 := by
  have hsum : ∑ v, (f v + g v) = 0 := by
    rw [Finset.sum_add_distrib, hf, hg]; ring
  have hdiff : ∑ v, (f v - g v) = 0 := by
    rw [Finset.sum_sub_distrib, hf, hg]; ring
  have h1 := hlam (fun x => f x + g x) hsum
  have h2 := hlam (fun x => f x - g x) hdiff
  -- expand the two quadratic forms
  have e1 : bil A (fun x => f x + g x) (fun x => f x + g x)
      = bil A f f + bil A f g + (bil A g f + bil A g g) := by
    rw [bil_add_left, bil_add_right, bil_add_right]
  have e2 : bil A (fun x => f x - g x) (fun x => f x - g x)
      = bil A f f - bil A f g - (bil A g f - bil A g g) := by
    have hneg : (fun x => f x - g x) = (fun x => f x + (-1 : ℝ) * g x) := by
      funext x; ring
    rw [hneg, bil_add_left, bil_add_right, bil_add_right, bil_smul_left, bil_smul_right,
      bil_smul_right, bil_smul_left]
    ring
  have hfg : bil A g f = bil A f g := (bil_symm A hsymm g f)
  rw [e1, hfg] at h1
  rw [e2, hfg] at h2
  have q1 : ∑ v, ((fun x => f x + g x) v) ^ 2
      = (∑ v, (f v) ^ 2) + 2 * (∑ v, f v * g v) + (∑ v, (g v) ^ 2) := by
    simp only []
    rw [show (∑ v, (f v + g v) ^ 2)
        = ∑ v, ((f v) ^ 2 + 2 * (f v * g v) + (g v) ^ 2) from
      Finset.sum_congr rfl (fun v _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have q2 : ∑ v, ((fun x => f x - g x) v) ^ 2
      = (∑ v, (f v) ^ 2) - 2 * (∑ v, f v * g v) + (∑ v, (g v) ^ 2) := by
    simp only []
    rw [show (∑ v, (f v - g v) ^ 2)
        = ∑ v, ((f v) ^ 2 - 2 * (f v * g v) + (g v) ^ 2) from
      Finset.sum_congr rfl (fun v _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [q1] at h1
  rw [q2] at h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The key spectral bound: `|bil A f g| ≤ lam * ‖f‖ * ‖g‖` for `f, g` orthogonal to constants. -/
