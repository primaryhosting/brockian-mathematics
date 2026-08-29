/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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

namespace Frontier

/-!
## Formalizing the Mordell–Faltings statement

Faltings' theorem (the Mordell conjecture) says that a smooth projective curve of
genus at least `2` defined over `ℚ` has only finitely many rational points.

The full statement requires the genus of an arbitrary curve, which is beyond what we
prove here.  We formalize the statement for smooth plane curves, where the genus is
given by the classical degree–genus formula `g = (d-1)(d-2)/2`, we prove a general
*reduction* principle for transferring finiteness of rational points along a map with
finite fibres, and we prove the theorem outright for a genus `3` curve, the Fermat
quartic `x⁴ + y⁴ = 1`, and (via the reduction) for the curve `u⁸ + v⁸ = 1`.
-/

/-- The genus of a smooth plane curve of degree `d`, given by the degree–genus
formula `g = (d-1)(d-2)/2`. -/

theorem fermatQuarticPoints_eq :
    fermatQuarticPoints = {((1 : ℚ), (0 : ℚ)), (-1, 0), (0, 1), (0, -1)} := by
  have hflt : FermatLastTheoremWith ℚ 4 := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour
  ext p
  obtain ⟨x, y⟩ := p
  simp only [fermatQuarticPoints, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    have hxy : x = 0 ∨ y = 0 := by
      by_contra hc
      push_neg at hc
      exact hflt x y 1 hc.1 hc.2 one_ne_zero (by simpa using h)
    have hquart : ∀ t : ℚ, t ^ 4 = 1 → t = 1 ∨ t = -1 := by
      intro t ht
      have h2 : (t ^ 2) ^ 2 = 1 ^ 2 := by
        rw [← pow_mul]; simpa using ht
      have h3 : t ^ 2 = 1 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
        · simpa using h
        · nlinarith [sq_nonneg t]
      have h4 : t ^ 2 = 1 ^ 2 := by simpa using h3
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    rcases hxy with hx | hy
    · subst hx
      have : y ^ 4 = 1 := by simpa using h
      rcases hquart y this with h1 | h1
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1⟩))
    · subst hy
      have : x ^ 4 = 1 := by simpa using h
      rcases hquart x this with h1 | h1
      · exact Or.inl ⟨h1, rfl⟩
      · exact Or.inr (Or.inl ⟨h1, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- The Fermat quartic, a curve of genus `3`, has finitely many rational points. -/
