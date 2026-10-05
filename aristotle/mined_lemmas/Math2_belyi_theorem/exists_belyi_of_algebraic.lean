import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma exists_belyi_of_algebraic (T : Finset ℂ) (h : ∀ t ∈ T, IsAlgebraic ℚ t) :
    ∃ f : ℚ[X], IsBelyi f ∧ ∀ t ∈ T, aeval t f ∈ ({0, 1} : Set ℂ) := by
  obtain ⟨f₁, hf₁deg, hf₁eval, hf₁crit⟩ :=
    exists_reduce_to_rat (T.sup degQ) T.card T h (fun t ht => Finset.le_sup ht)
      (Finset.card_filter_le _ _)
  have hder : derivative f₁ ≠ 0 := by
    intro hcon
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
    omega
  set U : Finset ℂ := T.image (fun t => aeval t f₁) ∪ critValFinset f₁ with hU
  have hU1 : ∀ u ∈ U, degQ u = 1 := by
    intro u hu
    rcases Finset.mem_union.mp hu with hh | hh
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hh
      exact hf₁eval t ht
    · exact hf₁crit u (by rw [critVal_eq_coe_critValFinset f₁ hder]; exact_mod_cast hh)
  set T₂ : Finset ℚ := U.image ratOf with hT₂
  obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := exists_belyi_rat T₂.card T₂ le_rfl
  have key : ∀ u ∈ U, aeval u g ∈ ({0, 1} : Set ℂ) := by
    intro u hu
    have h1 : ((ratOf u : ℚ) : ℂ) = u := ratOf_spec (hU1 u hu)
    have h2 : ratOf u ∈ T₂ := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    rw [← h1, aeval_ratCast]
    rcases hgeval _ h2 with hh | hh <;> rw [hh] <;> simp
  refine ⟨g.comp f₁, ⟨?_, ?_⟩, ?_⟩
  · rw [natDegree_comp]; exact Nat.mul_pos hgdeg hf₁deg
  · intro v hv
    rcases critVal_comp g f₁ hv with ⟨u, hu, huv⟩ | hv'
    · rw [← huv]
      refine key u (Finset.mem_union_right _ ?_)
      rw [critVal_eq_coe_critValFinset f₁ hder] at hu
      exact_mod_cast hu
    · exact hgcrit hv'
  · intro t ht
    rw [aeval_comp]
    exact key _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))

/-- **Belyi's theorem** for the projective line with marked points.

A finite set `S` of points of `ℙ¹(ℂ)` is defined over `ℚ̄` — i.e. all of its points are
algebraic numbers — if and only if there is a Belyi map `f : ℙ¹ → ℙ¹`, defined over `ℚ` and
ramified only over `{0, 1, ∞}`, carrying `S` into `{0, 1, ∞}`.

Belyi maps are realised here as polynomials `f ∈ ℚ[X]`.  Such a map is totally ramified over
`∞`, so `f` is ramified only over `{0,1,∞}` exactly when all of its finite critical values lie
in `{0,1}`; this is the content of `Math2.IsBelyi`.

The forward implication is Belyi's construction: first map the marked points into `ℚ` using
minimal polynomials (`Math2.exists_reduce_to_rat`), then map the resulting rational points into
`{0,1}` using the Belyi polynomials `c ⬝ x^p (1-x)^q` (`Math2.exists_belyi_rat`); in both steps
the critical values created along the way are pushed into the target as well.  The reverse
implication is immediate: a point mapped to `0` or `1` by a nonconstant `f ∈ ℚ[X]` is a root of
a nonzero rational polynomial. -/
