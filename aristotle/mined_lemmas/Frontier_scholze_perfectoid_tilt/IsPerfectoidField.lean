import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped NNReal
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

/-! ## The tilt

For a multiplicative monoid `R` and an exponent `p`, the *tilt* of `R` is the inverse limit
`lim_{x ↦ xᵖ} R`, realised as the monoid of sequences `(x₀, x₁, x₂, …)` with `xₙ₊₁ᵖ = xₙ`.
For a perfectoid field `K` this is Scholze's `K♭` (described through its multiplicative
monoid; in characteristic `p` the addition is the pointwise one). -/
structure Tilt (R : Type*) [Monoid R] (p : ℕ) where
  /-- The `n`-th component of a compatible system of `p`-power roots. -/
  coeff : ℕ → R
  /-- Compatibility: the `(n+1)`-st component is a `p`-th root of the `n`-th one. -/
  pow_coeff_succ : ∀ n : ℕ, coeff (n + 1) ^ p = coeff n

namespace Tilt

variable {R : Type*} {p : ℕ}

@[ext]

theorem IsPerfectoidField.pow_bijective_of_charP {p : ℕ} {K : Type*} [Field K]
    {v : Valuation K ℝ≥0} (hK : IsPerfectoidField p K v) [CharP K p] :
    Function.Bijective (fun x : K => x ^ p) := by
  haveI : Fact p.Prime := ⟨hK.prime⟩
  haveI : ExpChar K p := ExpChar.prime hK.prime
  have hp0 : ((p : K)) = 0 := by
    exact_mod_cast (CharP.cast_eq_zero K p)
  -- surjectivity on the valuation ring
  have hsurj_int : ∀ x : K, v x ≤ 1 → ∃ y : K, y ^ p = x := by
    intro x hx
    obtain ⟨y, -, hy⟩ := hK.frobenius_surjective x hx
    rw [hp0, map_zero, le_zero_iff, Valuation.zero_iff] at hy
    exact ⟨y, sub_eq_zero.mp hy⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    have : (frobenius K p) a = (frobenius K p) b := by
      simpa [frobenius_def] using hab
    exact frobenius_inj K p this
  · intro x
    rcases le_or_gt (v x) 1 with hx | hx
    · exact hsurj_int x hx
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hvx : v x ≠ 0 := by simpa [Valuation.zero_iff] using hx0
      have hinv : v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        rw [inv_le_one₀ (by positivity)]
        · exact hx.le
      obtain ⟨y, hy⟩ := hsurj_int x⁻¹ hinv
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow hK.prime.ne_zero] at hy
        exact (inv_ne_zero hx0) hy.symm
      refine ⟨y⁻¹, ?_⟩
      show (y⁻¹) ^ p = x
      rw [inv_pow, hy, inv_inv]

/-! ## The tilting statement -/

/--
**Scholze's tilting correspondence for perfectoid fields (statement, with the
characteristic-`p` base case proved).**

Let `K` be a perfectoid field with rank-one valuation `v` and residue characteristic `p`,
and let `K♭ = Tilt K p = lim_{x ↦ xᵖ} K` be its tilt.  Then:

1. `K♭` is *perfect*: the `p`-power map on `K♭` is bijective.
2. The "sharp" map `♯ : K♭ → K`, `f ↦ f⁰`, is multiplicative, so `x ↦ v (x♯)` is a
   multiplicative (rank-one) valuation on `K♭`.
3. `K♭` is multiplicatively a field: every element with `f⁰ ≠ 0` is a unit.
4. *(Base case of the tilting equivalence.)* If `K` itself has characteristic `p`, then
   tilting is the identity: `♯ : K♭ ≃* K` is an isomorphism, and it is additive for the
   pointwise addition of `K♭` (which is well defined in characteristic `p`), i.e. it is an
   isomorphism of fields `K♭ ≅ K`.
-/
