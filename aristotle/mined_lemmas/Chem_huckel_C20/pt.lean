import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

noncomputable def pt : ℂ[X] := ∏ k ∈ range 20, (X - C (w ^ k + w ^ (20 - k)))

/-- The composition `pt (X + X¹⁹)` is divisible by `X²⁰ - 1`. -/
