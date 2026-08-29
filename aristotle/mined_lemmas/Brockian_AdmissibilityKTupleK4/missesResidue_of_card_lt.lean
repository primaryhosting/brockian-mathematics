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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` (thought of as a tuple of shifts `h₁ < ⋯ < h_k`) is
*admissible* if for every prime `p` the elements of `H` do not cover all residue classes
modulo `p`; equivalently, some residue class mod `p` is missed by `H`.  This is the
classical admissibility condition from the Hardy–Littlewood prime `k`-tuple conjecture. -/

theorem missesResidue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime) (hcard : H.card < p) :
    ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h1 : (H.image (fun h : ℤ => (h : ZMod p))).card < (Finset.univ : Finset (ZMod p)).card := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ = (Finset.univ : Finset (ZMod p)).card := by simp [Finset.card_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  refine ⟨a, ?_⟩
  intro h hh hcon
  exact ha (Finset.mem_image.2 ⟨h, hh, hcon⟩)

/-- **Admissibility criterion for `4`-tuples.**
A `4`-element set of integers is admissible (i.e. misses a residue class modulo *every*
prime) as soon as it misses a residue class modulo the primes `2` and `3`.  All larger
primes are automatically fine, since `4` integers cannot cover `p ≥ 5` residue classes. -/
