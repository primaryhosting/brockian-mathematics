/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

/-- A tuple of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the residues of the entries
of `H` modulo `p` do not cover all of `ZMod p`. -/

theorem exists_residue_not_hit (H : List ℤ) (p : ℕ) (hp : p.Prime)
    (hlen : H.length < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set S : Finset (ZMod p) := (H.map (fun h : ℤ => (h : ZMod p))).toFinset with hS
  have hcard : S.card < Fintype.card (ZMod p) := by
    have h1 : S.card ≤ (H.map (fun h : ℤ => (h : ZMod p))).length :=
      List.toFinset_card_le _
    rw [List.length_map] at h1
    rw [ZMod.card]
    omega
  have hex : ∃ r : ZMod p, r ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S := fun x _ => hcon x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    omega
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, fun h hh hcast => hr ?_⟩
  rw [hS, List.mem_toFinset, List.mem_map]
  exact ⟨h, hh, hcast⟩

/-- The 4-tuple `(0, 2, 6, 8)` is admissible: for every prime `p` some residue class
modulo `p` is missed by `{0, 2, 6, 8}`. -/
