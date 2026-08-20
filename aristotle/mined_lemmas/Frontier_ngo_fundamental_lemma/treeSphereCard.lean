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

def treeSphereCard (q : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => ((q : Int) + 1) * qpow q k

/--
The number of vertices at distance at most `n` from a fixed vertex of the
`(q+1)`-regular tree.  For an elliptic regular semisimple `γ ∈ SL(2, F)` of the
unramified type with `val(disc γ) = 2n`, this is the number of `γ`-fixed vertices
modulo the action of `T(F)/T(O)`, i.e. the orbital integral `O_γ(1_K)`.
-/
