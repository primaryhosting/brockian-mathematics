/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

theorem holevo_bound_diagonal {X : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (q : X → n → ℝ) (hq0 : ∀ x i, 0 ≤ q x i) (hq1 : ∀ x, ∑ i, q x i = 1)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    mutualInfo (measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E)
      ≤ holevoChi p (fun x => diagonal fun i => (q x i : ℂ)) := by
  set M : n → Y → ℝ := fun i y => (E y i i).re with hMdef
  have hM0 : ∀ i y, 0 ≤ M i y := fun i y => (Complex.le_def.1 ((hE.1 y).diag_nonneg (i := i))).1
  have hM1 : ∀ i, ∑ y, M i y = 1 := by
    intro i
    have h : ∑ y, E y i i = (1 : ℂ) := by
      have := congrFun (congrFun hE.2 i) i
      simpa [Matrix.sum_apply] using this
    have h2 := congrArg Complex.re h
    rw [Complex.re_sum] at h2
    simpa [hMdef] using h2
  have hjoint : measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E
      = fun x y => ∑ i, (p x * q x i) * M i y := by
    funext x y
    rw [measJoint]
    have htr : Matrix.trace ((diagonal fun i => (q x i : ℂ)) * E y)
        = ∑ i, (q x i : ℂ) * E y i i := by
      simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    rw [htr, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [hMdef]; ring
  have hchi : holevoChi p (fun x => diagonal fun i => (q x i : ℂ))
      = shannonEntropy (fun i => ∑ x, p x * q x i) - ∑ x, p x * shannonEntropy (q x) := by
    rw [holevoChi]
    have havg : ∑ x, (p x : ℂ) • (diagonal fun i => (q x i : ℂ))
        = diagonal (fun i => ((∑ x, p x * q x i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.sum_apply]
    rw [havg, vonNeumannEntropy_diagonal]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  calc mutualInfo (fun x y => ∑ i, (p x * q x i) * M i y)
      ≤ mutualInfo (fun x i => p x * q x i) :=
        mutualInfo_channel_le _ (fun x i => mul_nonneg (hp0 x) (hq0 x i)) M hM0 hM1
    _ = _ := mutualInfo_mk p q hp0 hq0 hq1

/-- The characteristic polynomial is invariant under unitary conjugation. -/
