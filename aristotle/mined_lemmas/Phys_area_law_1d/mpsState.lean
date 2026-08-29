/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/

noncomputable def mpsState (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (n : ℕ) (s : Fin n → Fin d) : ℂ :=
  vL ⬝ᵥ (mpsProd A 0 n s *ᵥ vR)

/-- The matrix of amplitudes of a state on `k + m` sites, viewed across the cut between the
first `k` sites and the last `m` sites. Its singular values are the Schmidt coefficients of
the state across that cut. -/
