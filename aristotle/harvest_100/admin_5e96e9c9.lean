/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
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

set_option pp.structureInstances true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The tilt construction

For a field (more generally, a commutative monoid) `K` and a prime `p`, Scholze's *tilt*
`K♭` is, as a multiplicative monoid, the inverse limit

  `K♭ = lim (⋯ → K --x ↦ xᵖ--> K --x ↦ xᵖ--> K)`,

realised here as the submonoid of sequences `f : ℕ → K` with `f (n+1) ^ p = f n`.
This description of the underlying multiplicative monoid is characteristic-independent.
The multiplicative map `♯ : K♭ → K`, `f ↦ f 0`, is the *sharp* map.

Scholze's tilting equivalence asserts that `K ↦ K♭` is an equivalence between perfectoid
fields of mixed characteristic and perfectoid fields of characteristic `p`, compatible
with the Galois theory of the two sides.  Its *base case* — the content formalised and
proved below — is that on characteristic `p` perfectoid fields (i.e. perfect fields of
characteristic `p`) tilting is canonically the identity: the tilt is again a perfect ring
of characteristic `p`, and the sharp map is an isomorphism `K♭ ≃ K`.
-/

section Sequences

variable {K : Type*}

/-- A sequence of `p`-power-compatible elements: `f (n+1) ^ p = f n`. -/
def IsCompatible [Monoid K] (p : ℕ) (f : ℕ → K) : Prop := ∀ n, f (n + 1) ^ p = f n

variable [CommMonoid K] {p : ℕ}

lemma IsCompatible.shift {f : ℕ → K} (hf : IsCompatible p f) :
    IsCompatible p (fun n => f (n + 1)) := fun n => hf (n + 1)

lemma IsCompatible.pow_shift {f : ℕ → K} (hf : IsCompatible p f) :
    (fun n => f (n + 1) ^ p) = f := funext hf

/-- A compatible system of `p`-power roots over a ring in which `x ↦ xᵖ` is injective is
determined by its `0`-th term. -/
lemma IsCompatible.ext_zero (hp : Function.Injective (fun x : K => x ^ p))
    {f g : ℕ → K} (hf : IsCompatible p f) (hg : IsCompatible p g) (h0 : f 0 = g 0) :
    f = g := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
      have : f (n + 1) ^ p = g (n + 1) ^ p := by rw [hf n, hg n]; exact ih
      exact hp this

/-- If `x ↦ xᵖ` is surjective, every element of `K` is the `0`-th term of a compatible
system of `p`-power roots. -/
lemma exists_isCompatible (hp : Function.Surjective (fun x : K => x ^ p)) (a : K) :
    ∃ f : ℕ → K, IsCompatible p f ∧ f 0 = a := by
  set ρ : K → K := Function.surjInv hp with hρ
  have hρp : ∀ x : K, (ρ x) ^ p = x := fun x => Function.surjInv_eq hp x
  refine ⟨fun n => ρ^[n] a, ?_, rfl⟩
  intro n
  rw [Function.iterate_succ_apply']
  exact hρp _

/-- Two compatible systems with the same termwise `p`-th powers coincide. -/
lemma IsCompatible.eq_of_pow_eq {f g : ℕ → K} (hf : IsCompatible p f)
    (hg : IsCompatible p g) (h : ∀ n, f n ^ p = g n ^ p) : f = g := by
  funext n
  calc f n = f (n + 1) ^ p := (hf n).symm
    _ = g (n + 1) ^ p := h (n + 1)
    _ = g n := hg n

end Sequences

/-- The multiplicative monoid underlying the tilt `K♭` of a commutative monoid `K`:
sequences `f : ℕ → K` that are compatible under `p`-th powers. -/
def tiltMonoid (K : Type*) [CommMonoid K] (p : ℕ) : Submonoid (ℕ → K) where
  carrier := {f | IsCompatible p f}
  mul_mem' := by
    intro a b ha hb n
    simp [IsCompatible, Pi.mul_apply, mul_pow, ha n, hb n]
  one_mem' := by
    intro n
    simp

@[simp]
lemma mem_tiltMonoid {K : Type*} [CommMonoid K] {p : ℕ} {f : ℕ → K} :
    f ∈ tiltMonoid K p ↔ IsCompatible p f := Iff.rfl

/-- The *sharp* map `♯ : K♭ → K`, `f ↦ f 0`.  It is multiplicative. -/
def tiltSharp (K : Type*) [CommMonoid K] (p : ℕ) : tiltMonoid K p →* K where
  toFun f := (f : ℕ → K) 0
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma tiltSharp_apply {K : Type*} [CommMonoid K] {p : ℕ} (f : tiltMonoid K p) :
    tiltSharp K p f = (f : ℕ → K) 0 := rfl

/-- The tilt of any commutative monoid is *perfect*: raising to the `p`-th power is a
bijection on `K♭`, whatever the characteristic of `K`. -/
theorem tilt_pow_bijective (K : Type*) [CommMonoid K] (p : ℕ) :
    Function.Bijective (fun x : tiltMonoid K p => x ^ p) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have h' : ∀ n, f n ^ p = g n ^ p := by
      intro n
      exact congrFun (congrArg (fun x : tiltMonoid K p => (x : ℕ → K)) h) n
    exact Subtype.ext (hf.eq_of_pow_eq hg h')
  · rintro ⟨f, hf⟩
    exact ⟨⟨fun n => f (n + 1), hf.shift⟩, Subtype.ext hf.pow_shift⟩

/-!
## The tilt in characteristic `p`

In characteristic `p` the set of `p`-power-compatible sequences is not merely a submonoid
but a subring of `ℕ → K`, since Frobenius is additive.
-/

/-- The tilt of a commutative ring `K` of characteristic `p`, as a subring of `ℕ → K`. -/
def tiltSubring (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Subring (ℕ → K) where
  carrier := {f | IsCompatible p f}
  mul_mem' := by
    intro a b ha hb n
    simp [IsCompatible, Pi.mul_apply, mul_pow, ha n, hb n]
  one_mem' := by
    intro n
    simp
  add_mem' := by
    intro a b ha hb n
    have h : (a (n + 1) + b (n + 1)) ^ p = a (n + 1) ^ p + b (n + 1) ^ p :=
      add_pow_char _ _ p
    simp only [Pi.add_apply, h, ha n, hb n]
  zero_mem' := by
    intro n
    simp [zero_pow (Nat.Prime.ne_zero (Fact.out : p.Prime))]
  neg_mem' := by
    intro a ha n
    have h : ((0 : K) - a (n + 1)) ^ p = (0 : K) ^ p - a (n + 1) ^ p := sub_pow_char _ _
    simp only [Pi.neg_apply]
    have := ha n
    simp only [zero_sub, zero_pow (Nat.Prime.ne_zero (Fact.out : p.Prime))] at h
    rw [h, this]

@[simp]
lemma mem_tiltSubring {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : ℕ → K} : f ∈ tiltSubring K p ↔ IsCompatible p f := Iff.rfl

/-- In characteristic `p`, the subring `tiltSubring K p` and the tilt monoid have the same
underlying multiplicative monoid. -/
lemma tiltSubring_toSubmonoid (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    (tiltSubring K p).toSubmonoid = tiltMonoid K p := rfl

/-- Evaluation at the `0`-th component, as a ring homomorphism `K♭ → K`. -/
def tiltSharpRingHom (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    tiltSubring K p →+* K :=
  (Pi.evalRingHom (fun _ : ℕ => K) 0).comp (tiltSubring K p).subtype

@[simp]
lemma tiltSharpRingHom_apply {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : tiltSubring K p) : tiltSharpRingHom K p f = (f : ℕ → K) 0 := rfl

section Perfect

variable (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

lemma pow_bijective_of_perfect : Function.Bijective (fun x : K => x ^ p) := by
  have := PerfectRing.bijective_frobenius (R := K) (p := p)
  simpa [frobenius] using this

/-- Over a perfect ring of characteristic `p`, the sharp map is injective: a compatible
system of `p`-power roots is determined by its `0`-th term. -/
lemma tiltSharpRingHom_injective : Function.Injective (tiltSharpRingHom K p) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  exact Subtype.ext (hf.ext_zero (pow_bijective_of_perfect K p).1 hg h)

/-- Over a perfect ring of characteristic `p`, the sharp map is surjective: every element
admits a compatible system of `p`-power roots. -/
lemma tiltSharpRingHom_surjective : Function.Surjective (tiltSharpRingHom K p) := by
  intro a
  obtain ⟨f, hf, hf0⟩ := exists_isCompatible (p := p) (pow_bijective_of_perfect K p).2 a
  exact ⟨⟨f, hf⟩, hf0⟩

/-- The sharp map of the tilt monoid is bijective over a perfect ring of characteristic
`p`. -/
lemma tiltSharp_bijective : Function.Bijective (tiltSharp K p) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    exact Subtype.ext (hf.ext_zero (pow_bijective_of_perfect K p).1 hg h)
  · intro a
    obtain ⟨f, hf, hf0⟩ := exists_isCompatible (p := p) (pow_bijective_of_perfect K p).2 a
    exact ⟨⟨f, hf⟩, hf0⟩

/-- The tilt subring in characteristic `p` is again perfect. -/
lemma tiltSubring_pow_bijective :
    Function.Bijective (fun x : tiltSubring K p => x ^ p) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have h' : ∀ n, f n ^ p = g n ^ p := fun n =>
      congrFun (congrArg (fun x : tiltSubring K p => (x : ℕ → K)) h) n
    exact Subtype.ext (hf.eq_of_pow_eq hg h')
  · rintro ⟨f, hf⟩
    exact ⟨⟨fun n => f (n + 1), hf.shift⟩, Subtype.ext hf.pow_shift⟩

end Perfect

/-- **Base case of Scholze's tilting equivalence.**

Let `K` be a perfectoid field of characteristic `p`, i.e. a perfect field of
characteristic `p` (Frobenius bijective).  Then:

* the tilt `K♭ = lim_{x ↦ xᵖ} K` is itself perfect: `x ↦ xᵖ` is bijective on `K♭`
  (this holds for the tilt of *any* commutative monoid, in any characteristic);
* the sharp map `♯ : K♭ → K`, `f ↦ f 0`, is a multiplicative bijection, and in fact a
  ring isomorphism `K♭ ≃+* K` for the (characteristic `p`) ring structure on the tilt;
* consequently `K♭` again has characteristic `p` and is perfect.

So on characteristic `p` perfectoid fields the tilting functor is canonically the
identity — the base case of Scholze's tilting equivalence. -/
theorem scholze_perfectoid_tilt (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectRing K p] :
    Function.Bijective (fun x : tiltMonoid K p => x ^ p) ∧
      Function.Bijective (tiltSharp K p) ∧
      ∃ e : tiltSubring K p ≃+* K,
        (∀ f : tiltSubring K p, e f = (f : ℕ → K) 0) ∧
        Function.Bijective (fun x : tiltSubring K p => x ^ p) ∧
        CharP (tiltSubring K p) p := by
  have hinj := tiltSharpRingHom_injective K p
  have hbij : Function.Bijective (tiltSharpRingHom K p) :=
    ⟨hinj, tiltSharpRingHom_surjective K p⟩
  refine ⟨tilt_pow_bijective K p, tiltSharp_bijective K p,
    RingEquiv.ofBijective (tiltSharpRingHom K p) hbij, fun f => rfl,
    tiltSubring_pow_bijective K p, charP_of_injective_ringHom hinj p⟩

end Frontier

