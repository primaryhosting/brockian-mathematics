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

lemma admissible_iff_localFactor_pos (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → 0 < localFactor H p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have hne : H.image (fun x => x % p) ≠ Finset.range p := by
      intro hEq
      have : r ∈ H.image (fun x => x % p) := by
        rw [hEq]; exact Finset.mem_range.2 hrp
      obtain ⟨h', hh', he⟩ := Finset.mem_image.1 this
      exact hr h' hh' he
    have hsub : H.image (fun x => x % p) ⊆ Finset.range p := by
      intro y hy
      obtain ⟨h', _, he⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (he ▸ Nat.mod_lt _ hp.pos)
    have hlt : (H.image (fun x => x % p)).card < p := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
      simpa using this
    have : ((H.image (fun x => x % p)).card : ℚ) < p := by exact_mod_cast hlt
    have : ((H.image (fun x => x % p)).card : ℚ) / p < 1 := by
      rw [div_lt_one hppos]; exact this
    simp only [localFactor]
    linarith
  · intro hH p hp
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have := hH p hp
    simp only [localFactor] at this
    have hlt : ((H.image (fun x => x % p)).card : ℚ) < p := by
      have h1 : ((H.image (fun x => x % p)).card : ℚ) / p < 1 := by linarith
      rwa [div_lt_one hppos] at h1
    have hlt' : (H.image (fun x => x % p)).card < p := by exact_mod_cast hlt
    have hne : ¬ (Finset.range p ⊆ H.image (fun x => x % p)) := by
      intro hsub
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    rw [Finset.subset_iff] at hne
    push_neg at hne
    obtain ⟨r, hr, hr'⟩ := hne
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h' hh' he
    exact hr' (Finset.mem_image.2 ⟨h', hh', he⟩)

/-- An explicit family of admissible triples `{0, a, d}`: only the primes `2` and `3` need to
be inspected, the remaining ones are handled by the pigeonhole principle. -/
