/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`. -/

theorem entropy_concave_stdSimplex (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (gibbsEntropy (ι := ι)) :=
  (entropy_concave ι).subset (fun _ hp => hp.1) (convex_stdSimplex ℝ ι)

end Chem

