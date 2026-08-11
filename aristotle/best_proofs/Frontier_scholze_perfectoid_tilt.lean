/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/
def Tilt : Subring (ℕ → R) where
  carrier := {f : ℕ → R | ∀ n, f (n + 1) ^ p = f n}
  mul_mem' := by
    intro a b ha hb n
    simpa [mul_pow] using congrArg₂ (· * ·) (ha n) (hb n)
  one_mem' := by intro n; simp
  add_mem' := by
    intro a b ha hb n
    have := add_pow_char (a (n + 1)) (b (n + 1)) p
    simp only [Pi.add_apply]
    rw [this, ha n, hb n]
  zero_mem' := by intro n; simp [zero_pow (Nat.Prime.pos (Fact.out (p := p.Prime))).ne']
  neg_mem' := by
    intro a ha n
    have hneg : ∀ x : R, (-x) ^ p = -(x ^ p) := by
      intro x; simpa [frobenius_def] using map_neg (frobenius R p) x
    simp only [Pi.neg_apply]
    rw [hneg, ha n]

variable {p R}

@[simp] lemma Tilt.pow_succ_apply (f : Tilt p R) (n : ℕ) :
    (f : ℕ → R) (n + 1) ^ p = (f : ℕ → R) n := f.2 n

/-- The **sharp map** `♯ : R♭ → R`, i.e. projection onto the `0`-th component. -/
def Tilt.sharp : Tilt p R →+* R where
  toFun f := (f : ℕ → R) 0
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma Tilt.sharp_apply (f : Tilt p R) : Tilt.sharp f = (f : ℕ → R) 0 := rfl

instance : CharP (ℕ → R) p :=
  ⟨fun n => by
    constructor
    · intro h
      have h0 : ((n : ℕ → R)) 0 = 0 := by rw [h]; rfl
      simp only [Pi.natCast_apply] at h0
      exact (CharP.cast_eq_zero_iff R p n).1 h0
    · intro h
      funext k
      simpa using (CharP.cast_eq_zero_iff R p n).2 h⟩

/-- The tilt has characteristic `p`. -/
instance Tilt.charP : CharP (Tilt p R) p := CharP.subring (ℕ → R) p (Tilt p R)

lemma Tilt.coe_pow (f : Tilt p R) (n k : ℕ) : ((f ^ k : Tilt p R) : ℕ → R) n = ((f : ℕ → R) n) ^ k :=
  rfl

/-- Frobenius is injective on the tilt. -/
theorem tilt_frobenius_injective : Function.Injective (frobenius (Tilt p R) p) := by
  intro f g h
  have hcoe : ∀ n, ((f : ℕ → R) n) ^ p = ((g : ℕ → R) n) ^ p := by
    intro n
    have := congrArg (fun x : Tilt p R => (x : ℕ → R) n) h
    simpa [frobenius_def, Tilt.coe_pow] using this
  apply Subtype.ext
  funext n
  calc (f : ℕ → R) n = ((f : ℕ → R) (n + 1)) ^ p := (f.2 n).symm
    _ = ((g : ℕ → R) (n + 1)) ^ p := hcoe (n + 1)
    _ = (g : ℕ → R) n := g.2 n

/-- Frobenius is surjective on the tilt. -/
theorem tilt_frobenius_surjective : Function.Surjective (frobenius (Tilt p R) p) := by
  intro f
  refine ⟨⟨fun n => (f : ℕ → R) (n + 1), fun n => f.2 (n + 1)⟩, ?_⟩
  apply Subtype.ext
  funext n
  simp [frobenius_def, Tilt.coe_pow]

/-- **The tilt is a perfect ring of characteristic `p`.** -/
theorem tilt_frobenius_bijective : Function.Bijective (frobenius (Tilt p R) p) :=
  ⟨tilt_frobenius_injective, tilt_frobenius_surjective⟩

instance Tilt.perfectRing : PerfectRing (Tilt p R) p := ⟨tilt_frobenius_bijective⟩

end Tilt

/-! ## Base case: in characteristic `p`, tilting is the identity -/

section CharPCase

variable {p : ℕ} {R : Type*} [CommRing R] [Fact p.Prime] [CharP R p]
  (hperf : Function.Bijective (frobenius R p))

/-- The inverse of Frobenius on a perfect ring: the `p`-th root map. -/
noncomputable def pRoot : R ≃+* R := (RingEquiv.ofBijective (frobenius R p) hperf).symm

@[simp] lemma pRoot_pow (x : R) : (pRoot hperf x) ^ p = x := by
  have h : frobenius R p (pRoot hperf x) = x :=
    (RingEquiv.ofBijective (frobenius R p) hperf).apply_symm_apply x
  simpa [frobenius_def] using h

@[simp] lemma pRoot_of_pow (x : R) : pRoot hperf (x ^ p) = x := by
  have h : pRoot hperf (frobenius R p x) = x :=
    (RingEquiv.ofBijective (frobenius R p) hperf).symm_apply_apply x
  rw [frobenius_def] at h
  exact h

/-- For a perfect ring `R` of characteristic `p`, the canonical map `R → R♭`,
`x ↦ (x, x^{1/p}, x^{1/p²}, …)`, is a ring isomorphism whose inverse is the sharp map. -/
noncomputable def tiltEquivOfPerfect : R ≃+* Tilt p R := by
  refine
    { toFun := fun x => ⟨fun n => (pRoot hperf)^[n] x, ?_⟩
      invFun := fun f => (f : ℕ → R) 0
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · intro n
    show ((pRoot hperf)^[n + 1] x) ^ p = (pRoot hperf)^[n] x
    rw [Function.iterate_succ_apply', pRoot_pow]
  · intro x; rfl
  · intro f
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] ((f : ℕ → R) 0) = (f : ℕ → R) n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← f.2 n, pRoot_of_pow]
  · intro x y
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] (x * y) = ((pRoot hperf)^[n] x) * ((pRoot hperf)^[n] y)
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact map_mul (pRoot hperf) _ _
  · intro x y
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] (x + y) = ((pRoot hperf)^[n] x) + ((pRoot hperf)^[n] y)
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact map_add (pRoot hperf) _ _

@[simp] lemma sharp_tiltEquivOfPerfect (x : R) :
    Tilt.sharp (tiltEquivOfPerfect hperf x) = x := rfl

end CharPCase

/-! ## Perfectoid fields -/

/-- A **perfectoid field**: a field `K`, complete with respect to a rank-one nonarchimedean
valuation `v` which is nontrivial and non-discrete, of residue characteristic `p`, and such that
the Frobenius `x ↦ x^p` is surjective on `𝒪_K / p 𝒪_K`. -/
structure IsPerfectoidField (p : ℕ) (K : Type*) (Γ₀ : Type*) [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `K` is complete for the valuation topology. -/
  complete : CompleteSpace K
  /-- The valuation is nontrivial. -/
  nontrivial : ∃ x : K, Valued.v x ≠ (0 : Γ₀) ∧ Valued.v x ≠ 1
  /-- The value group is non-discrete: values accumulate at `1` from below. -/
  nondiscrete : ∀ x : K, Valued.v x ≠ (0 : Γ₀) → Valued.v x < 1 →
    ∃ y : K, Valued.v x < Valued.v y ∧ Valued.v y < (1 : Γ₀)
  /-- The residue characteristic is `p`. -/
  residue_char : Valued.v (p : K) < (1 : Γ₀)
  /-- Frobenius is surjective on `𝒪_K / p 𝒪_K`. -/
  frobenius_surjective :
    ∀ x : K, Valued.v x ≤ (1 : Γ₀) →
      ∃ y z : K, Valued.v y ≤ (1 : Γ₀) ∧ Valued.v z ≤ (1 : Γ₀) ∧ x - y ^ p = (p : K) * z

section PerfectoidCharP

variable {p : ℕ} {K : Type*} {Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] [Fact p.Prime] [CharP K p]

/-- **A perfectoid field of characteristic `p` is perfect.** -/
theorem frobenius_bijective_of_perfectoid_charP (hK : IsPerfectoidField p K Γ₀) :
    Function.Bijective (frobenius K p) := by
  have hp : (p : K) = 0 := CharP.cast_eq_zero K p
  have hsurj_int : ∀ x : K, Valued.v x ≤ (1 : Γ₀) → ∃ y : K, y ^ p = x := by
    intro x hx
    obtain ⟨y, z, _, _, hyz⟩ := hK.frobenius_surjective x hx
    exact ⟨y, by have hz : x - y ^ p = 0 := by rw [hyz, hp, zero_mul]
                 linear_combination -hz⟩
  refine ⟨frobenius_inj K p, ?_⟩
  intro x
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [frobenius_def, hx0, zero_pow (Nat.Prime.pos (Fact.out (p := p.Prime))).ne']⟩
  by_cases hx : Valued.v x ≤ (1 : Γ₀)
  · obtain ⟨y, hy⟩ := hsurj_int x hx
    exact ⟨y, by simpa [frobenius_def] using hy⟩
  · push_neg at hx
    have hinv : Valued.v x⁻¹ ≤ (1 : Γ₀) := by
      rw [map_inv₀]
      exact le_of_lt (by
        rw [inv_lt_one₀ (lt_of_le_of_lt zero_le' hx)]
        exact hx)
    obtain ⟨y, hy⟩ := hsurj_int x⁻¹ hinv
    refine ⟨y⁻¹, ?_⟩
    simp only [frobenius_def, inv_pow, hy, inv_inv]

/-- Conversely, a complete perfect valued field of characteristic `p` with nontrivial,
non-discrete valuation is perfectoid.  So in equal characteristic `p`, "perfectoid" is exactly
"perfect". -/
theorem isPerfectoidField_of_perfect [CompleteSpace K]
    (hperf : Function.Bijective (frobenius K p))
    (hnt : ∃ x : K, Valued.v x ≠ (0 : Γ₀) ∧ Valued.v x ≠ 1)
    (hnd : ∀ x : K, Valued.v x ≠ (0 : Γ₀) → Valued.v x < 1 →
      ∃ y : K, Valued.v x < Valued.v y ∧ Valued.v y < (1 : Γ₀)) :
    IsPerfectoidField p K Γ₀ where
  prime := Fact.out
  complete := ‹CompleteSpace K›
  nontrivial := hnt
  nondiscrete := hnd
  residue_char := by rw [CharP.cast_eq_zero K p, map_zero]; exact zero_lt_one
  frobenius_surjective := by
    intro x hx
    have hpow : Valued.v (pRoot hperf x) ^ p = (Valued.v x : Γ₀) := by rw [← map_pow, pRoot_pow]
    have hy : Valued.v (pRoot hperf x) ≤ (1 : Γ₀) := by
      by_contra hc
      push_neg at hc
      have h1 : 1 < Valued.v (pRoot hperf x) ^ p :=
        one_lt_pow₀ hc (Nat.Prime.pos (Fact.out (p := p.Prime))).ne'
      rw [hpow] at h1
      exact absurd hx (not_le.2 h1)
    exact ⟨pRoot hperf x, 0, hy, by simp, by simp [pRoot_pow]⟩

end PerfectoidCharP

/-! ## The tilting theorem (base case) -/

/--
**Scholze's tilting for perfectoid fields — formalized statement and characteristic `p` base
case.**

For any commutative ring `R` of characteristic `p`, the tilt `R♭ = lim_{x ↦ x^p} R` is a ring of
characteristic `p` on which Frobenius is bijective (a perfect ring); this is the general
construction underlying Scholze's tilting equivalence.

For a perfectoid field `K` of characteristic `p` (the base case of the tilting equivalence,
where the tilting functor is the identity), the canonical map `K → K♭` is a ring isomorphism
inverted by the sharp map `♯ : K♭ → K`; in particular `K ≅ K♭` as fields.
-/
theorem scholze_perfectoid_tilt
    {p : ℕ} [Fact p.Prime] {K : Type*} {Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CharP K p]
    (hK : IsPerfectoidField p K Γ₀) :
    -- the tilt of any characteristic-`p` ring is a perfect ring of characteristic `p`
    (∀ (R : Type) (_ : CommRing R) (_ : CharP R p),
        CharP (Tilt p R) p ∧ Function.Bijective (frobenius (Tilt p R) p)) ∧
    -- Frobenius is bijective on a characteristic-`p` perfectoid field
    Function.Bijective (frobenius K p) ∧
    -- and tilting is (canonically) the identity on such a field
    ∃ e : K ≃+* Tilt p K, ∀ x : K, Tilt.sharp (e x) = x := by
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _
    exact ⟨Tilt.charP, tilt_frobenius_bijective⟩
  · exact frobenius_bijective_of_perfectoid_charP hK
  · exact ⟨tiltEquivOfPerfect (frobenius_bijective_of_perfectoid_charP hK), fun x => rfl⟩


/-! ## The tilt in mixed characteristic

For a perfectoid field `K` of any characteristic, the ring of integers of the tilt `K♭` is
constructed as the inverse limit of Frobenius on `𝒪_K / p 𝒪_K`.  We check here that this ring
is well defined and is a perfect ring of characteristic `p`.
-/

section MixedChar

/-- A nontrivial commutative ring in which a prime `p` vanishes has characteristic `p`. -/
theorem charP_of_prime_cast_eq_zero (A : Type*) [CommRing A] [Nontrivial A] (p : ℕ)
    (hp : p.Prime) (h : (p : A) = 0) : CharP A p := by
  obtain ⟨q, hq⟩ := CharP.exists A
  have hqp : q ∣ p := (CharP.cast_eq_zero_iff A q p).1 h
  have hq1 : q ≠ 1 := CharP.char_ne_one A q
  rcases Nat.Prime.eq_one_or_self_of_dvd hp q hqp with h1 | h2
  · exact absurd h1 hq1
  · subst h2; exact hq

variable {p : ℕ} {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- The ring `𝒪_K / p 𝒪_K` attached to a valued field. -/
abbrev residuePMod (v : Valuation K Γ₀) (p : ℕ) : Type _ :=
  v.integer ⧸ (Ideal.span {(p : v.integer)})

instance residuePMod.instNontrivial [Fact (v (p : K) < 1)] : Nontrivial (residuePMod v p) := by
  have hnu : ¬ IsUnit (p : v.integer) := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ : ∃ w : v.integer, (p : v.integer) * w = 1 := ⟨u.inv, by rw [← hu]; simp⟩
    have hK : (p : K) * (w : K) = 1 := by
      have := congrArg (fun x : v.integer => (x : K)) hw
      simpa using this
    have h1 : v ((p : K) * (w : K)) = 1 := by rw [hK]; simp
    have hlt : v (p : K) * v (w : K) < 1 :=
      calc v (p : K) * v (w : K) ≤ v (p : K) * 1 := by gcongr; exact w.2
        _ = v (p : K) := mul_one _
        _ < 1 := Fact.out
    rw [map_mul] at h1
    exact absurd h1 (ne_of_lt hlt)
  exact Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)

instance residuePMod.instCharP [Fact p.Prime] [Fact (v (p : K) < 1)] :
    CharP (residuePMod v p) p := by
  refine charP_of_prime_cast_eq_zero _ p Fact.out ?_
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : v.integer)})) p]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- **The ring of integers of the tilt.**  For a valued field `K` with residue characteristic `p`
(in particular for any perfectoid field, of mixed or equal characteristic), the inverse limit of
Frobenius on `𝒪_K / p 𝒪_K` is a perfect ring of characteristic `p`. -/
theorem tilt_integers_perfect [Fact p.Prime] [Fact (v (p : K) < 1)] :
    CharP (Tilt p (residuePMod v p)) p ∧
      Function.Bijective (frobenius (Tilt p (residuePMod v p)) p) :=
  ⟨Tilt.charP, tilt_frobenius_bijective⟩

end MixedChar

end Frontier

