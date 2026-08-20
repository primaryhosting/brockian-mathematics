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

theorem fundamentalLemma_prodDatum {D E : EndoscopicDatum}
    (hD : FundamentalLemmaHolds D) (hE : FundamentalLemmaHolds E) :
    FundamentalLemmaHolds (prodDatum D E) := by
  intro f gH gG h
  have h' : (match D.norm gH.1, E.norm gH.2 with
      | some a, some b => some (a, b)
      | _, _ => none) = some gG := h
  revert h'
  cases hD' : D.norm gH.1 with
  | none => intro h'; simp at h'
  | some a =>
    cases hE' : E.norm gH.2 with
    | none => intro h'; simp at h'
    | some b =>
      intro h'
      have hab : (a, b) = gG := by
        simpa using h'
      have h1 := hD f.1 gH.1 a hD'
      have h2 := hE f.2 gH.2 b hE'
      subst hab
      show D.transferFactor gH.1 * E.transferFactor gH.2 *
          (D.stableOrbitalIntegral (D.satakeTransfer f.1) gH.1 *
            E.stableOrbitalIntegral (E.satakeTransfer f.2) gH.2)
        = D.kappaOrbitalIntegral f.1 a * E.kappaOrbitalIntegral f.2 b
      rw [← h1, ← h2]
      grind

/-! ### Invariance under isomorphism of data -/

/--
Transport of the fundamental lemma along an isomorphism of endoscopic data:
if all the ingredients of `E` are obtained from those of `D` through bijections
of the class sets and of the Hecke algebras, then the fundamental lemma for `D`
implies it for `E`.
-/
