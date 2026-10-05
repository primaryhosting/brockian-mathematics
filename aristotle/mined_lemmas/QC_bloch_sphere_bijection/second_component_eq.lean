/-
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/

lemma second_component_eq {a b c d : ℂ}
    (hac : normSq a = normSq c) (hcd : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d)
    (ha : a ≠ 0) : d = (c / a) * b := by
  have hc : c ≠ 0 := by intro h; apply ha; rw [h] at hac; simpa using hac
  have hcc : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  have h1 : c * (starRingEnd ℂ) c = ((normSq c : ℝ) : ℂ) := Complex.mul_conj c
  have h2 : a * (starRingEnd ℂ) a = ((normSq a : ℝ) : ℂ) := Complex.mul_conj a
  have hacC : ((normSq a : ℝ) : ℂ) = ((normSq c : ℝ) : ℂ) := by rw [hac]
  have key : d * a = c * b := by
    apply mul_right_cancel₀ hcc
    linear_combination (-a) * hcd + b * h2 - b * h1 + b * hacC
  field_simp
  linear_combination key

/-- Qubit states with the same Bloch vector differ by a global phase. -/
