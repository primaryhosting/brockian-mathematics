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

theorem fundamentalLemma_trivialDatum (C A : Type) (O : A → C → Int) :
    FundamentalLemmaHolds (trivialDatum C A O) := by
  intro f gH gG h
  have hg : gH = gG := by
    simpa [trivialDatum] using h
  subst hg
  simp [trivialDatum]

/-! ### Reduction to the factors of a product -/

/-- The product of two endoscopic data, `H₁ × H₂` inside `G₁ × G₂`. -/
