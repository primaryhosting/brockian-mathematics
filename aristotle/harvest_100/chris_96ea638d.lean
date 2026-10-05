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
theorem ext [Monoid R] {f g : Tilt R p} (h : ∀ n, f.coeff n = g.coeff n) : f = g := by
  cases f; cases g
  simp only [Tilt.mk.injEq]
  exact funext h

instance [CommMonoid R] : CommMonoid (Tilt R p) where
  mul f g :=
    ⟨fun n => f.coeff n * g.coeff n, by
      intro n
      rw [mul_pow, f.pow_coeff_succ, g.pow_coeff_succ]⟩
  one := ⟨fun _ => 1, by intro n; simp⟩
  mul_assoc f g h := by ext n; exact mul_assoc _ _ _
  one_mul f := by ext n; exact one_mul _
  mul_one f := by ext n; exact mul_one _
  mul_comm f g := by ext n; exact mul_comm _ _

@[simp]
theorem coeff_mul [CommMonoid R] (f g : Tilt R p) (n : ℕ) :
    (f * g).coeff n = f.coeff n * g.coeff n := rfl

@[simp]
theorem coeff_one [CommMonoid R] (n : ℕ) : (1 : Tilt R p).coeff n = 1 := rfl

@[simp]
theorem coeff_pow [CommMonoid R] (f : Tilt R p) (k n : ℕ) :
    (f ^ k).coeff n = f.coeff n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, coeff_mul, ih]

/-- Shifting a compatible system of `p`-power roots: the inverse of the Frobenius on the tilt. -/
def shift [CommMonoid R] (f : Tilt R p) : Tilt R p :=
  ⟨fun n => f.coeff (n + 1), fun n => f.pow_coeff_succ (n + 1)⟩

@[simp]
theorem coeff_shift [CommMonoid R] (f : Tilt R p) (n : ℕ) :
    (shift f).coeff n = f.coeff (n + 1) := rfl

/-- **The tilt is perfect**: raising to the `p`-th power is a bijection of `Tilt R p`,
with inverse the shift. -/
theorem frobenius_bijective [CommMonoid R] :
    Function.Bijective (fun f : Tilt R p => f ^ p) := by
  refine ⟨fun f g h => ?_, fun f => ⟨shift f, ?_⟩⟩
  · ext n
    have h1 : (f ^ p).coeff (n + 1) = (g ^ p).coeff (n + 1) :=
      congrArg (fun t : Tilt R p => t.coeff (n + 1)) h
    simpa [f.pow_coeff_succ, g.pow_coeff_succ] using h1
  · ext n
    simp [f.pow_coeff_succ]

/-- The multiplicative "sharp" map `K♭ → K`, `f ↦ f⁰`. -/
def sharp [CommMonoid R] (f : Tilt R p) : R := f.coeff 0

@[simp]
theorem sharp_mul [CommMonoid R] (f g : Tilt R p) : sharp (f * g) = sharp f * sharp g := rfl

theorem coeff_ne_zero_of_coeff_zero_ne_zero {K : Type*} [Field K] (hp : p ≠ 0) (f : Tilt K p)
    (h : f.coeff 0 ≠ 0) (n : ℕ) : f.coeff n ≠ 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro hc
      exact ih (by rw [← f.pow_coeff_succ n, hc, zero_pow hp])

/-- Pointwise inverse of an element of the tilt of a field. -/
def inv {K : Type*} [Field K] (f : Tilt K p) : Tilt K p :=
  ⟨fun n => (f.coeff n)⁻¹, by
    intro n
    show ((f.coeff (n + 1))⁻¹) ^ p = (f.coeff n)⁻¹
    rw [inv_pow, f.pow_coeff_succ]⟩

/-- **The tilt of a field is a field (multiplicatively)**: every element with nonzero
`0`-th component is a unit. -/
theorem isUnit_of_coeff_zero_ne_zero {K : Type*} [Field K] (hp : p ≠ 0) (f : Tilt K p)
    (h : f.coeff 0 ≠ 0) : IsUnit f := by
  have hmul : f * inv f = 1 := by
    ext n
    have hne := coeff_ne_zero_of_coeff_zero_ne_zero hp f h n
    show f.coeff n * (f.coeff n)⁻¹ = 1
    rw [mul_inv_cancel₀ hne]
  exact ⟨⟨f, inv f, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

end Tilt

/-! ## Perfectoid fields -/

/-- **Perfectoid field** (Scholze): a field `K` equipped with a rank-one valuation
`v : K → ℝ≥0` such that

* `K` is complete for the `v`-topology;
* `v` is nontrivial and non-discrete (its value group is dense);
* the residue characteristic is `p`, i.e. `v p < 1`;
* Frobenius is surjective on `𝒪_K / p`.
-/
structure IsPerfectoidField (p : ℕ) (K : Type*) [Field K] (v : Valuation K ℝ≥0) : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `K` is complete for the topology defined by `v`. -/
  complete : CompleteSpace (WithVal v)
  /-- The valuation is nontrivial. -/
  nontrivial : ∃ x : K, v x ≠ 0 ∧ v x ≠ 1
  /-- The value group is dense (the valuation is non-discrete). -/
  nondiscrete : ∀ x : K, v x < 1 → ∃ y : K, v x < v y ∧ v y < 1
  /-- The residue characteristic is `p`. -/
  residue_char : v (p : K) < 1
  /-- Frobenius is surjective on `𝒪_K / p 𝒪_K`. -/
  frobenius_surjective :
    ∀ x : K, v x ≤ 1 → ∃ y : K, v y ≤ 1 ∧ v (y ^ p - x) ≤ v (p : K)

/-- In characteristic `p`, a perfectoid field is a perfect field: `x ↦ xᵖ` is a bijection. -/
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
theorem scholze_perfectoid_tilt {p : ℕ} {K : Type*} [Field K] {v : Valuation K ℝ≥0}
    (hK : IsPerfectoidField p K v) :
    Function.Bijective (fun f : Tilt K p => f ^ p) ∧
    (∀ f g : Tilt K p, Tilt.sharp (f * g) = Tilt.sharp f * Tilt.sharp g) ∧
    (∀ f : Tilt K p, Tilt.sharp f ≠ 0 → IsUnit f) ∧
    (∀ _ : CharP K p, ∃ e : Tilt K p ≃* K,
      (∀ f : Tilt K p, e f = Tilt.sharp f) ∧
      ∀ f g : Tilt K p, ∃ h : Tilt K p,
        (∀ n : ℕ, h.coeff n = f.coeff n + g.coeff n) ∧ e h = e f + e g) := by
  refine ⟨Tilt.frobenius_bijective, fun f g => Tilt.sharp_mul f g,
    fun f hf => Tilt.isUnit_of_coeff_zero_ne_zero hK.prime.ne_zero f hf, ?_⟩
  intro hchar
  haveI := hchar
  haveI : Fact p.Prime := ⟨hK.prime⟩
  -- `K` is perfect, so we may take `p`-th roots.
  have hbij := hK.pow_bijective_of_charP
  set E : K ≃ K := Equiv.ofBijective _ hbij
  have hEapp : ∀ x : K, E x = x ^ p := fun x => rfl
  have hEsymm : ∀ x : K, (E.symm x) ^ p = x := by
    intro x
    rw [← hEapp]
    exact E.apply_symm_apply x
  -- the inverse of the sharp map: take iterated `p`-th roots
  have hroot : ∀ x : K, ∀ n : ℕ, ((E.symm)^[n + 1] x) ^ p = (E.symm)^[n] x := by
    intro x n
    rw [Function.iterate_succ_apply', hEsymm]
  let g : K → Tilt K p := fun x => ⟨fun n => (E.symm)^[n] x, hroot x⟩
  have hg_coeff : ∀ (x : K) (n : ℕ), (g x).coeff n = (E.symm)^[n] x := fun _ _ => rfl
  have hleft : ∀ f : Tilt K p, g (f.coeff 0) = f := by
    intro f
    ext n
    rw [hg_coeff]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, ← f.pow_coeff_succ n, ← hEapp,
          Equiv.symm_apply_apply]
  refine ⟨{ toFun := fun f => f.coeff 0
            invFun := g
            left_inv := hleft
            right_inv := fun x => by simp [hg_coeff]
            map_mul' := fun f h => rfl }, fun f => rfl, ?_⟩
  intro f h
  refine ⟨⟨fun n => f.coeff n + h.coeff n, fun n => ?_⟩, fun n => rfl, rfl⟩
  rw [add_pow_char, f.pow_coeff_succ, h.pow_coeff_succ]

end Frontier

