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

theorem ramsey_3_3 : RamseyProp 6 3 3 :=
  RamseyProp.step (ramsey_two_left 3) (RamseyProp.symm (ramsey_two_left 3)) (by norm_num)

/-- `R(3,4) ≤ 9`. -/
