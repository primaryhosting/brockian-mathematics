import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

namespace QC

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/

lemma bloch_injective_aux (v w : Qubit) (h : blochVec v.val = blochVec w.val) : v ≈ w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨a', b'⟩, hv'⟩ := w
  simp only at h hv hv' ⊢
  have h0 : 2 * ((starRingEnd ℂ) a * b).re = 2 * ((starRingEnd ℂ) a' * b').re :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 0) h
  have h1 : 2 * ((starRingEnd ℂ) a * b).im = 2 * ((starRingEnd ℂ) a' * b').im :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 1) h
  have h2 : normSq a - normSq b = normSq a' - normSq b' :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 2) h
  have hna : normSq a = normSq a' := by linarith
  have hcj : (starRingEnd ℂ) a * b = (starRingEnd ℂ) a' * b' :=
    Complex.ext (by linarith) (by linarith)
  exact phase_of_data a b a' b' hv hv' hna hcj

