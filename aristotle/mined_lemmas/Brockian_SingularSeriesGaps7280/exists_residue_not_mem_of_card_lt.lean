import Mathlib
/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other piece of syntax,
-- including module doc comments, so the required header appears immediately after
-- the single `import Mathlib` line.

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of natural numbers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`.  Equivalently, the local factor of the
singular series attached to `H` at `p` is nonzero for every prime `p`. -/

theorem exists_residue_not_mem_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℕ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hr⟩
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- **Admissibility of prime gap ranges.**  For any window length `L` and any starting point
`N > L`, the set of primes lying in the interval `[N, N + L)` is an admissible tuple. -/
