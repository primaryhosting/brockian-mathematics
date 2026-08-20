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

theorem fundamentalLemma_transport {D E : EndoscopicDatum}
    (hD : FundamentalLemmaHolds D)
    (uH : E.HClass → D.HClass) (uG : D.GClass → E.GClass)
    (uf : E.HeckeG → D.HeckeG)
    (hnorm : ∀ gH, E.norm gH = (D.norm (uH gH)).map uG)
    (hΔ : ∀ gH, E.transferFactor gH = D.transferFactor (uH gH))
    (hSO : ∀ f gH, E.stableOrbitalIntegral (E.satakeTransfer f) gH
      = D.stableOrbitalIntegral (D.satakeTransfer (uf f)) (uH gH))
    (hO : ∀ f gG, E.kappaOrbitalIntegral f (uG gG) = D.kappaOrbitalIntegral (uf f) gG) :
    FundamentalLemmaHolds E := by
  intro f gH gG h
  rw [hnorm gH] at h
  cases hD' : D.norm (uH gH) with
  | none => rw [hD'] at h; simp at h
  | some a =>
    rw [hD'] at h
    have hag : uG a = gG := by simpa using h
    subst hag
    rw [hΔ gH, hSO f gH, hO f a]
    exact hD (uf f) (uH gH) a hD'

/-! ### The Bruhat–Tits tree counts for the `SL(2)` base case -/

/-- `qpow q k = q ^ k`, as an integer. -/
