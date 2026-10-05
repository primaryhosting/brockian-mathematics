/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integer shifts `H` *avoids* the prime `p` when the shifts do not cover
all residue classes modulo `p`. -/

theorem avoidsPrime_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime) (hcard : H.card < p) :
    AvoidsPrime H p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  simp only [AvoidsPrime, not_exists, not_forall, not_ne_iff] at hcon
  have hsurj : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsurj) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card] at hle
  omega

/-- **Reduction to small primes.** To check admissibility of a `k`-element set of shifts it
suffices to check the primes `p ≤ k`.  (The proof splits on whether `p ≤ H.card`.) -/
