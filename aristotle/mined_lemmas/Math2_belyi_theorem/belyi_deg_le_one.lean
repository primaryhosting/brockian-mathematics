import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_deg_le_one (S : Finset ℂ) (halg : ∀ s ∈ S, IsAlgebraic ℚ s)
    (hdeg : ∀ s ∈ S, adeg s ≤ 1) : BelyiFor (S : Set ℂ) := by
  classical
  have key : ∀ s ∈ S, ∃ q : ℚ, (q : ℂ) = s := by
    intro s hs
    have hint : IsIntegral ℚ s := (halg s hs).isIntegral
    have hpos : 0 < (minpoly ℚ s).natDegree := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ s).natDegree = 1 := le_antisymm (hdeg s hs) hpos
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact ⟨q, by simpa using hq⟩
  choose! g hg using key
  refine belyi_mono ?_ (belyi_rat (S.image g))
  rintro s hs
  exact ⟨g s, by simpa using ⟨s, hs, rfl⟩, hg s hs⟩

/-- Inductive step of the descent, at fixed maximal degree `d + 1 ≥ 2`: applying the minimal
polynomial of a point of maximal degree strictly decreases the number of points of that degree,
while introducing only critical values of smaller degree. -/
