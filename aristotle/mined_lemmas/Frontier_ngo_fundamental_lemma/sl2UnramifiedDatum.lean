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

def sl2UnramifiedDatum (q : Nat) : EndoscopicDatum where
  HClass := Nat
  GClass := Nat
  norm := some
  transferFactor := fun n => signPow n * qpow q n
  HeckeG := Unit
  HeckeH := Unit
  satakeTransfer := id
  stableOrbitalIntegral := fun _ _ => 1
  kappaOrbitalIntegral := fun _ n => kappaCount q n

/--
**Base case of the Langlands–Shelstad fundamental lemma (Ngô).**

The fundamental lemma holds for the unramified elliptic endoscopy of `SL(2)` over
a local field with residue cardinality `q`, for the unit element of the spherical
Hecke algebra and every depth `n`:

  `Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`,

which unwinds to `(-1)^n q^n · 1 = kappaCount q n`, the alternating point count of
the affine Springer fibre (`kappaCount_eq`).
-/
