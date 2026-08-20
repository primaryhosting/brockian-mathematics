/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 does not permit a module
-- docstring before `import`; the same header is repeated as a module docstring below.)


import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture: the singular series `𝔖(H)` is nonzero exactly for such `H`)
if for every prime `p` the reductions of the elements of `H` modulo `p` miss at least one
residue class. -/

theorem admissible_pair_of_even (d : ℤ) (hd : Even d) : Admissible {0, d} := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    have hh' : h = 0 ∨ h = d := by simpa using hh
    have hzero : ((d : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).2 (by exact_mod_cast hd.two_dvd)
    rcases hh' with rfl | rfl
    · simp
    · rw [hzero]
      exact zmod_two_zero_ne_one
  · have hcard : ({0, d} : Finset ℤ).card < p := by
      have h1 : ({0, d} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p ≠ 2 := hp2
      omega
    exact exists_missed_residue_of_card_lt _ p hcard

/-- The tuple `{0, 2, 6, 8, 9098}` misses the residue `1` modulo `2`. -/
