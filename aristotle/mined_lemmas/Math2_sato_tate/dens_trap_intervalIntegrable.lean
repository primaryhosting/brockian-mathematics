/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma dens_trap_intervalIntegrable (u v ε a b : ℝ) :
    IntervalIntegrable (fun x => satoTateDensity x * trap u v ε x) MeasureTheory.volume a b :=
  (continuous_satoTateDensity.mul (continuous_trap u v ε)).intervalIntegrable _ _

