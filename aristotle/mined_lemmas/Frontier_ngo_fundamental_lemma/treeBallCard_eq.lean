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

theorem treeBallCard_eq (q : Nat) : ∀ n : Nat,
    ((q : Int) - 1) * treeBallCard q n = ((q : Int) + 1) * qpow q n - 2
  | 0 => by show ((q : Int) - 1) * 1 = ((q : Int) + 1) * 1 - 2; grind
  | n + 1 => by
    have ih := treeBallCard_eq q n
    show ((q : Int) - 1) * (treeBallCard q n + treeSphereCard q (n + 1))
      = ((q : Int) + 1) * qpow q (n + 1) - 2
    rw [show treeSphereCard q (n + 1) = ((q : Int) + 1) * qpow q n from rfl,
      show qpow q (n + 1) = (q : Int) * qpow q n from rfl]
    grind

/--
The alternating (`κ`-weighted) count of the ball of radius `n` in the
`(q+1)`-regular tree collapses to `(-1)^n q^n`.  This cancellation is the
arithmetic content of the fundamental lemma for the unramified elliptic
endoscopy of `SL(2)`.
-/
