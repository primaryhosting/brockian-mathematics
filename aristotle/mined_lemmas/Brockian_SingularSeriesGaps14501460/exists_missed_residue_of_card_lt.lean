/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of natural numbers `H` is *admissible* if for every prime `p` it misses at
least one residue class modulo `p`.  Equivalently (see `admissible_iff_localFactor_pos`), all
local factors of the associated singular series are strictly positive. -/

lemma exists_missed_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (h : H.card < p) :
    ∃ r < p, ∀ h' ∈ H, h' % p ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.range p ⊆ H.image (fun x => x % p) := by
    intro r hr
    simp only [Finset.mem_range] at hr
    obtain ⟨h', hh', he⟩ := hcon r hr
    exact Finset.mem_image.2 ⟨h', hh', he⟩
  have h1 : p ≤ (H.image (fun x => x % p)).card := by
    simpa using Finset.card_le_card hsub
  have h2 : (H.image (fun x => x % p)).card ≤ H.card := Finset.card_image_le
  omega

/-- Admissibility is exactly the positivity of all local factors of the singular series. -/
