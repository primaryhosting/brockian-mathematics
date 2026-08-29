/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical information quantities -/

section ClassicalDefs

variable {X I Y : Type*}

/-- Shannon entropy `H(P) = -∑ P x * log (P x)` of a finite probability vector. -/

theorem holevo_bound_povm (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (d : I → X → ℝ) (hd : ∀ i, IsDensity (Matrix.diagonal (fun x => (d i x : ℂ))))
    (E : Y → Matrix X X ℂ) (hE : IsPOVM E) :
    mutualInfo (measuredJoint p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) E)
      ≤ holevoChi p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) := by
  set M : X → Y → ℝ := fun x y => ((E y) x x).re with hMdef
  have hd0 : ∀ i x, 0 ≤ d i x := by
    intro i x
    have := posSemidef_diag_re_nonneg (hd i).1 x
    simpa [Matrix.diagonal_apply_eq] using this
  have hd1 : ∀ i, ∑ x, d i x = 1 := by
    intro i
    have h := (hd i).2
    rw [Matrix.trace_diagonal] at h
    have := congrArg Complex.re h
    simpa [Complex.re_sum] using this
  have hM0 : ∀ x y, 0 ≤ M x y := fun x y => posSemidef_diag_re_nonneg (hE.1 y) x
  have hM1 : ∀ x, ∑ y, M x y = 1 := by
    intro x
    have h := congrArg (fun A : Matrix X X ℂ => A x x) hE.2
    simp only [Matrix.sum_apply, Matrix.one_apply_eq] at h
    have := congrArg Complex.re h
    simpa [Complex.re_sum, hMdef] using this
  have hjoint : measuredJoint p (fun i => Matrix.diagonal (fun x => (d i x : ℂ))) E
      = fun i y => p i * ∑ x, d i x * M x y := by
    funext i y
    rw [measuredJoint]
    congr 1
    rw [Matrix.trace]
    simp [Matrix.diagonal_mul, Complex.re_sum, hMdef]
  have hchi : holevoChi p (fun i => Matrix.diagonal (fun x => (d i x : ℂ)))
      = shannonEntropy (fun x => ∑ j, p j * d j x) - ∑ i, p i * shannonEntropy (d i) := by
    rw [holevoChi]
    congr 1
    · have hsum : ∑ i, (p i : ℂ) • Matrix.diagonal (fun x => (d i x : ℂ))
          = Matrix.diagonal (fun x => ((∑ i, p i * d i x : ℝ) : ℂ)) := by
        ext x y
        rw [Matrix.sum_apply]
        by_cases h : x = y
        · subst h
          simp [Matrix.diagonal_apply_eq, Complex.ofReal_sum]
        · simp [Matrix.diagonal_apply_ne _ h]
      rw [hsum, vonNeumannEntropy_diagonal]
    · exact Finset.sum_congr rfl fun i _ => by rw [vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  exact classical_holevo_bound p hp d hd0 hd1 M hM0 hM1

/-- **Holevo bound**: the accessible information of an ensemble of commuting states is at most
its Holevo χ quantity. -/
