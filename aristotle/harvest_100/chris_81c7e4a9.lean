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

/-- A finite set of integers `H` is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, the reductions of the elements of
`H` modulo `p` do not cover all residue classes mod `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- For a prime `p` strictly larger than the size of `H`, admissibility at `p` is automatic:
the image of `H` in `ZMod p` is too small to be everything. -/
theorem admissible_at_large_prime (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  -- every residue class is attained, so `ZMod p` embeds into the image of `H`
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro a _
    obtain ⟨h, hh, rfl⟩ := hcon a
    exact Finset.mem_image_of_mem _ hh
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card] at h1
  exact absurd h1 (not_le.mpr hcard)

/-- The classical admissible `4`-tuple `{0, 2, 6, 8}`: it has four elements, its diameter is
`8`, and it is admissible, i.e. for every prime `p` some residue class mod `p` is missed. -/
theorem AdmissibilityKTupleK4 :
    ({0, 2, 6, 8} : Finset ℤ).card = 4 ∧ Admissible ({0, 2, 6, 8} : Finset ℤ) := by
  refine ⟨by decide, ?_⟩
  intro p hp
  have hcard : ({0, 2, 6, 8} : Finset ℤ).card = 4 := by decide
  rcases lt_or_ge p 5 with hlt | hge
  · -- small primes: `p = 2` or `p = 3`
    interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · -- p = 2 : every element is even, so `1` is missed
      refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> decide
    · -- p = 3 : residues are `0, 2, 0, 2`, so `1` is missed
      refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> decide
    · exact absurd hp (by decide)
  · exact admissible_at_large_prime _ p hp (by omega)

end Brockian

