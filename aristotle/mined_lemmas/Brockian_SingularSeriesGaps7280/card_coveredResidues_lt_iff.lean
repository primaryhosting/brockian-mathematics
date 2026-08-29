import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The residues modulo `p` covered by the tuple `H`. -/

theorem card_coveredResidues_lt_iff {H : Finset ℕ} {p : ℕ} [NeZero p] :
    (coveredResidues H p).card < p ↔ ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hcard
    by_contra hcon
    push_neg at hcon
    have huniv : coveredResidues H p = Finset.univ := by
      refine Finset.eq_univ_of_forall (fun r => ?_)
      obtain ⟨h, hh, hr⟩ := hcon r
      exact mem_coveredResidues.mpr ⟨h, hh, hr⟩
    rw [huniv, Finset.card_univ, ZMod.card] at hcard
    exact lt_irrefl _ hcard
  · rintro ⟨r, hr⟩
    have hne : r ∉ coveredResidues H p := by
      intro hmem
      obtain ⟨h, hh, rfl⟩ := mem_coveredResidues.mp hmem
      exact hr h hh rfl
    have hss : coveredResidues H p ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (fun hcon => hne (hcon ▸ Finset.mem_univ r))
    have := Finset.card_lt_card hss
    rwa [Finset.card_univ, ZMod.card] at this

/-- Admissibility is equivalent to the non-vanishing of every local singular-series factor. -/
