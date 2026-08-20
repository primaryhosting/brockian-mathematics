/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

def RamseySet : Set ℕ :=
  {N : ℕ | ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 4 s)}

/-- **The Ramsey number `R(4,4)` equals `18`**: every two-colouring of the edges of the
complete graph on `18` vertices contains a monochromatic `K₄`, and `18` is the least such
number (the Paley graph on `17` vertices witnesses that `17` vertices are not enough). -/
