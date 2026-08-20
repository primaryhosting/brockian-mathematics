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

def prodDatum (D E : EndoscopicDatum) : EndoscopicDatum where
  HClass := D.HClass × E.HClass
  GClass := D.GClass × E.GClass
  norm := fun p =>
    match D.norm p.1, E.norm p.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  transferFactor := fun p => D.transferFactor p.1 * E.transferFactor p.2
  HeckeG := D.HeckeG × E.HeckeG
  HeckeH := D.HeckeH × E.HeckeH
  satakeTransfer := fun f => (D.satakeTransfer f.1, E.satakeTransfer f.2)
  stableOrbitalIntegral := fun f p =>
    D.stableOrbitalIntegral f.1 p.1 * E.stableOrbitalIntegral f.2 p.2
  kappaOrbitalIntegral := fun f p =>
    D.kappaOrbitalIntegral f.1 p.1 * E.kappaOrbitalIntegral f.2 p.2

/--
Reduction of the fundamental lemma for a product of endoscopic data to the
fundamental lemma for each factor.
-/
