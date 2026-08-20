/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file states the Langlands–Shelstad fundamental lemma (proved in general by
Ngô Bảo Châu) in the following shape, and proves a base case together with two
Lean-checked reductions.

For an unramified endoscopic datum `(H, s, η)` for a reductive group `G` over a
non-archimedean local field `F`, with `q` the residue cardinality, the fundamental

def kappaCount (q : Nat) : Nat → Int
  | 0 => 1
  | n + 1 => kappaCount q n + signPow (n + 1) * treeSphereCard q (n + 1)

/-- Closed formula for the number of vertices of a ball in the `(q+1)`-regular tree:
`(q - 1) * #B(n) = (q + 1) * q ^ n - 2`, i.e. `#B(n) = 1 + (q+1)(q^n - 1)/(q - 1)`. -/
