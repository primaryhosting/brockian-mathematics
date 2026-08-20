import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

noncomputable def C5adj : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- For every `k`, the number `2 cos(2πk/5)` is an eigenvalue of `C5adj`, with
eigenvector `(ω^j)_{j<5}` where `ω = exp(2πik/5)`. -/
