/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- A finite set of nonnegative integers is *admissible* (in the Hardy–Littlewood /
Hensley–Richards sense) if for every prime `p` it fails to cover all residue classes
modulo `p`.  Equivalently, the singular series attached to the tuple is nonzero. -/

theorem sieved_witness (q0 d k : ℕ) (hk1 : 100 ≤ k) (hk2 : k ≤ 140)
    (hcard : (sieved q0 d).card = k)
    (h0 : 0 ∈ sieved q0 d) (hd : d ∈ sieved q0 d) :
    ∃ H : Finset ℕ, Admissible H ∧ 100 ≤ H.card ∧ 0 ∈ H ∧ d ∈ H ∧ ∀ h ∈ H, h ≤ d :=
  ⟨sieved q0 d, sieved_admissible q0 d (by omega), by omega, h0, hd,
    fun _ hh => sieved_subset_range hh⟩

