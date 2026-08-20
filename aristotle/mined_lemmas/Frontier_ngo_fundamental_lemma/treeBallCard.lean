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

def treeBallCard (q : Nat) : Nat → Int
  | 0 => 1
  | n + 1 => treeBallCard q n + treeSphereCard q (n + 1)

/--
The same ball, counted with the sign `κ` (the parity of the distance to the
central vertex): this is the `κ`-orbital integral `O^κ_γ(1_K)`.
-/
