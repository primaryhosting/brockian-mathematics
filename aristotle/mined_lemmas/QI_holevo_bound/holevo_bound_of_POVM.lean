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

theorem holevo_bound_of_POVM {X : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hcomm : SimultaneouslyDiagonalizable ρ)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    mutualInfo (measJoint p ρ E) ≤ holevoChi p ρ := by
  obtain ⟨U, hU, hdiag⟩ := hcomm
  choose q hq using hdiag
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hDpsd : ∀ x, (diagonal (fun i => (q x i : ℂ))).PosSemidef := by
    intro x
    have h := ((hρ x).1).conjTranspose_mul_mul_same U
    rw [← Matrix.star_eq_conjTranspose, hq x] at h
    have hEq : star U * (U * diagonal (fun i => (q x i : ℂ)) * star U) * U
        = diagonal (fun i => (q x i : ℂ)) := by
      simp only [mul_assoc]
      rw [hUU, mul_one, ← mul_assoc, hUU, one_mul]
    rwa [hEq] at h
  have hq0 : ∀ x i, 0 ≤ q x i := by
    intro x i
    have h := (hDpsd x).diag_nonneg (i := i)
    rw [Matrix.diagonal_apply_eq] at h
    exact_mod_cast (Complex.le_def.1 h).1
  have hq1 : ∀ x, ∑ i, q x i = 1 := by
    intro x
    have htr : Matrix.trace (ρ x) = Matrix.trace (diagonal (fun i => (q x i : ℂ))) := by
      rw [hq x, mul_assoc, Matrix.trace_mul_comm, mul_assoc, hUU, mul_one]
    rw [(hρ x).2] at htr
    have : ∑ i, (q x i : ℂ) = 1 := by
      rw [htr]; simp [Matrix.trace, Matrix.diag]
    exact_mod_cast this
  set E' : Y → Matrix n n ℂ := fun y => star U * E y * U with hE'def
  have hE' : IsPOVM E' := by
    constructor
    · intro y
      rw [hE'def, Matrix.star_eq_conjTranspose]
      exact (hE.1 y).conjTranspose_mul_mul_same U
    · rw [hE'def]
      simp only
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.2, mul_one, hUU]
  have hjoint : measJoint p ρ E = measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E' := by
    funext x y
    rw [measJoint, measJoint]
    congr 2
    rw [hq x, mul_assoc, mul_assoc, Matrix.trace_mul_comm]
    congr 1
    simp only [hE'def, mul_assoc]
  have hchi : holevoChi p ρ = holevoChi p (fun x => diagonal fun i => (q x i : ℂ)) := by
    rw [holevoChi, holevoChi]
    have havg : ∑ x, (p x : ℂ) • ρ x
        = U * (∑ x, (p x : ℂ) • diagonal (fun i => (q x i : ℂ))) * star U := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by
        rw [hq x, Matrix.mul_smul, Matrix.smul_mul]
    rw [havg]
    have havg2 : ∑ x, (p x : ℂ) • (diagonal fun i => (q x i : ℂ))
        = diagonal (fun i => ((∑ x, p x * q x i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.sum_apply]
    rw [havg2, vonNeumannEntropy_unitary_conj_diagonal hU, vonNeumannEntropy_diagonal]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by
      rw [hq x, vonNeumannEntropy_unitary_conj_diagonal hU, vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  exact holevo_bound_diagonal p hp0 q hq0 hq1 E' hE'

/-- **The Holevo bound**: the accessible information of a quantum ensemble `{p x, ρ x}` (the
supremum, over all POVMs with outcomes in `Y`, of the mutual information between the label and
the measurement outcome) is at most the Holevo χ quantity of the ensemble.

The ensemble states are assumed to commute (formalized as being simultaneously diagonalizable
by a unitary).  The normalization hypothesis `hp1` on the weights is part of the definition of
an ensemble; the proof in fact never uses it. -/
