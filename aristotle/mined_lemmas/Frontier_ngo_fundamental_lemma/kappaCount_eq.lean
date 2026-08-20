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

theorem kappaCount_eq (q : Nat) : ∀ n : Nat,
    kappaCount q n = signPow n * qpow q n
  | 0 => by simp [kappaCount, signPow, qpow]
  | n + 1 => by
    have ih := kappaCount_eq q n
    show kappaCount q n + signPow (n + 1) * treeSphereCard q (n + 1)
      = signPow (n + 1) * qpow q (n + 1)
    rw [ih, show treeSphereCard q (n + 1) = ((q : Int) + 1) * qpow q n from rfl,
      show qpow q (n + 1) = (q : Int) * qpow q n from rfl,
      show signPow (n + 1) = -signPow n from rfl]
    grind

/-! ### The base case: unramified elliptic endoscopy of `SL(2)` -/

/--
The unramified elliptic endoscopic datum of `G = SL(2)` over a local field with
residue cardinality `q`: the endoscopic group is the elliptic unramified maximal
torus `H = T`, and `κ` is the nontrivial character of the group of connected
components.

Stable classes on either side are indexed by the depth `n`, where
`val(disc γ) = 2n`; the norm correspondence matches equal depths.  The transfer
factor is `Δ = (-1)^n q^n`; since `H` is a torus, the stable orbital integral of
the unit element of its spherical Hecke algebra is `1`; and the `κ`-orbital
integral of the unit element `1_K` of the spherical Hecke algebra of `G` is the
signed point count `kappaCount q n` of the affine Springer fibre, described by
the ball of radius `n` in the Bruhat–Tits tree.
-/
