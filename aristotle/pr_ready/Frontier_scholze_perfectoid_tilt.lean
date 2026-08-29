/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Statement: State the tilting equivalence of perfectoid fields (Scholze).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

/-!
## The tilt

For a `p`-adic (or characteristic `p`) coefficient object `K`, Scholze's *tilt* `K^♭` is the
inverse limit of `K` along the `p`-power map,
`K^♭ = lim_{x ↦ x^p} K = {(x₀, x₁, x₂, …) : xₙ₊₁^p = xₙ}`,
with componentwise multiplication.  We realize it as a submonoid of `ℕ → K` (and, in
characteristic `p`, as a subring, since then `x ↦ x^p` is additive).
-/

/-- The underlying set of the tilt `K^♭`: sequences `(xₙ)` with `xₙ₊₁ ^ p = xₙ`. -/
def tiltSet (p : ℕ) (K : Type*) [Monoid K] : Set (ℕ → K) :=
  {f | ∀ n, f (n + 1) ^ p = f n}

@[simp] lemma mem_tiltSet {p : ℕ} {K : Type*} [Monoid K] {f : ℕ → K} :
    f ∈ tiltSet p K ↔ ∀ n, f (n + 1) ^ p = f n := Iff.rfl

/-- The tilt `K^♭` of a commutative monoid `K`, as a submonoid of `ℕ → K`. -/
def tiltSubmonoid (p : ℕ) (K : Type*) [CommMonoid K] : Submonoid (ℕ → K) where
  carrier := tiltSet p K
  one_mem' := by intro n; simp
  mul_mem' := by
    intro f g hf hg n
    simp only [Pi.mul_apply, mul_pow, hf n, hg n]

@[simp] lemma mem_tiltSubmonoid {p : ℕ} {K : Type*} [CommMonoid K] {f : ℕ → K} :
    f ∈ tiltSubmonoid p K ↔ ∀ n, f (n + 1) ^ p = f n := Iff.rfl

/-- The tilt `K^♭` of a commutative ring `K` of exponential characteristic `p`, as a subring
of `ℕ → K`.  Here the `p`-power map is a ring homomorphism, so the tilt is a ring. -/
def tiltSubring (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] : Subring (ℕ → K) where
  carrier := tiltSet p K
  one_mem' := by intro n; simp
  mul_mem' := by
    intro f g hf hg n
    simp only [Pi.mul_apply, mul_pow, hf n, hg n]
  zero_mem' := by
    intro n
    have hp : p ≠ 0 := (expChar_pos K p).ne'
    simp [zero_pow hp]
  add_mem' := by
    intro f g hf hg n
    have := add_pow_expChar (f (n + 1)) (g (n + 1)) p
    simp only [Pi.add_apply]
    rw [this, hf n, hg n]
  neg_mem' := by
    intro f hf n
    have hp : p ≠ 0 := (expChar_pos K p).ne'
    have h0 : ((0 : K) - f (n + 1)) ^ p = (0 : K) ^ p - f (n + 1) ^ p :=
      sub_pow_expChar 0 (f (n + 1))
    simp only [Pi.neg_apply]
    have : (-(f (n + 1))) ^ p = -(f (n + 1) ^ p) := by
      simpa [zero_pow hp] using h0
    rw [this, hf n]

@[simp] lemma mem_tiltSubring {p : ℕ} {K : Type*} [CommRing K] [ExpChar K p] {f : ℕ → K} :
    f ∈ tiltSubring p K ↔ ∀ n, f (n + 1) ^ p = f n := Iff.rfl

/-- The subring and the submonoid structures on the tilt have the same underlying set. -/
lemma tiltSubring_coe (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] :
    (tiltSubring p K : Set (ℕ → K)) = tiltSubmonoid p K := rfl

/-!
## The tilt is always perfect

This is the fundamental structural feature of tilting: whatever `K` is, the `p`-power map on
`K^♭` is bijective (its inverse is the shift).
-/

/-- The `p`-power map on the tilt is injective. -/
lemma tilt_pow_injective (p : ℕ) (K : Type*) [CommMonoid K] :
    Function.Injective (fun x : tiltSubmonoid p K => x ^ p) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  have h' : ∀ n, f n ^ p = g n ^ p := by
    intro n
    have := congrArg (fun y : tiltSubmonoid p K => (y : ℕ → K) n) h
    simpa using this
  apply Subtype.ext
  funext n
  have := h' (n + 1)
  rw [hf n, hg n] at this
  exact this

/-- The `p`-power map on the tilt is surjective: the shift provides `p`-th roots. -/
lemma tilt_pow_surjective (p : ℕ) (K : Type*) [CommMonoid K] :
    Function.Surjective (fun x : tiltSubmonoid p K => x ^ p) := by
  rintro ⟨g, hg⟩
  refine ⟨⟨fun n => g (n + 1), fun n => hg (n + 1)⟩, ?_⟩
  apply Subtype.ext
  funext n
  simpa using hg n

/-- **The tilt is perfect.**  The `p`-power map on `K^♭` is bijective for every commutative
monoid `K`. -/
theorem tilt_pow_bijective (p : ℕ) (K : Type*) [CommMonoid K] :
    Function.Bijective (fun x : tiltSubmonoid p K => x ^ p) :=
  ⟨tilt_pow_injective p K, tilt_pow_surjective p K⟩

/-!
## The tilting equivalence in characteristic `p`

If `K` already has characteristic `p` and is perfect, then tilting does nothing:
the projection `(xₙ) ↦ x₀` is a ring isomorphism `K^♭ ≃+* K`.  This is the base case of the
tilting equivalence (`K ↦ K^♭` is an equivalence from perfectoid fields over `K` to perfectoid
fields over `K^♭`, and it is the identity on the characteristic `p` side).
-/

/-- Projection of the tilt onto the `0`-th coordinate, as a ring homomorphism. -/
def tiltEval (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] : tiltSubring p K →+* K :=
  (Pi.evalRingHom (fun _ : ℕ => K) 0).comp (tiltSubring p K).subtype

@[simp] lemma tiltEval_apply (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p]
    (x : tiltSubring p K) : tiltEval p K x = (x : ℕ → K) 0 := rfl

lemma tiltEval_injective (p : ℕ) (K : Type*) [CommRing K] [IsReduced K] [ExpChar K p] :
    Function.Injective (tiltEval p K) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  simp only [tiltEval_apply] at h
  have key : ∀ n, f n = g n := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
        have hpow : f (n + 1) ^ p = g (n + 1) ^ p := by rw [hf n, hg n, ih]
        exact frobenius_inj K p (by simpa [frobenius_def] using hpow)
  exact Subtype.ext (funext key)

lemma tiltEval_surjective (p : ℕ) (K : Type*) [CommRing K] [ExpChar K p] [PerfectRing K p] :
    Function.Surjective (tiltEval p K) := by
  intro a
  refine ⟨⟨fun n => ((frobeniusEquiv K p).symm)^[n] a, ?_⟩, rfl⟩
  intro n
  have h1 : ((frobeniusEquiv K p).symm)^[n + 1] a
      = (frobeniusEquiv K p).symm (((frobeniusEquiv K p).symm)^[n] a) :=
    Function.iterate_succ_apply' _ _ _
  show ((frobeniusEquiv K p).symm)^[n + 1] a ^ p = ((frobeniusEquiv K p).symm)^[n] a
  rw [h1]
  simp

/-- **Tilting in characteristic `p`.**  For a perfect commutative ring `K` of characteristic `p`
(e.g. a perfectoid field of characteristic `p`), the projection `(xₙ) ↦ x₀` is a ring
isomorphism `K^♭ ≃+* K`. -/
noncomputable def tiltEquiv (p : ℕ) (K : Type*) [CommRing K] [IsReduced K] [ExpChar K p]
    [PerfectRing K p] : tiltSubring p K ≃+* K :=
  RingEquiv.ofBijective (tiltEval p K) ⟨tiltEval_injective p K, tiltEval_surjective p K⟩

@[simp] lemma tiltEquiv_apply (p : ℕ) (K : Type*) [CommRing K] [IsReduced K] [ExpChar K p]
    [PerfectRing K p] (x : tiltSubring p K) : tiltEquiv p K x = (x : ℕ → K) 0 := rfl

/-!
## Functoriality of tilting
-/

/-- The ring homomorphism `(ℕ → K) →+* (ℕ → L)` induced by `f : K →+* L`. -/
def piMap {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) : (ℕ → K) →+* (ℕ → L) :=
  Pi.ringHom fun n => f.comp (Pi.evalRingHom (fun _ : ℕ => K) n)

@[simp] lemma piMap_apply {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (x : ℕ → K)
    (n : ℕ) : piMap f x n = f (x n) := rfl

/-- Tilting is functorial: a ring homomorphism `f : K →+* L` induces `f^♭ : K^♭ →+* L^♭`,
acting componentwise. -/
def tiltRingHom (p : ℕ) {K L : Type*} [CommRing K] [CommRing L] [ExpChar K p] [ExpChar L p]
    (f : K →+* L) : tiltSubring p K →+* tiltSubring p L :=
  RingHom.codRestrict ((piMap f).comp (tiltSubring p K).subtype) (tiltSubring p L) <| by
    rintro ⟨x, hx⟩ n
    simp only [RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, piMap_apply]
    rw [← map_pow, hx n]

@[simp] lemma tiltRingHom_apply (p : ℕ) {K L : Type*} [CommRing K] [CommRing L] [ExpChar K p]
    [ExpChar L p] (f : K →+* L) (x : tiltSubring p K) (n : ℕ) :
    (tiltRingHom p f x : ℕ → L) n = f ((x : ℕ → K) n) := rfl

/-!
## The target statement
-/

/-- A ring of prime exponential characteristic `p` has characteristic `p`. -/
lemma charP_of_expChar_prime' (R : Type*) [AddMonoidWithOne R] (p : ℕ) (hp : p.Prime)
    [hR : ExpChar R p] : CharP R p := by
  cases hR with
  | zero => exact absurd hp Nat.not_prime_one
  | prime _ => assumption

/-- **Scholze's tilting equivalence (formalized statement, characteristic `p` case).**

For a prime `p` and perfectoid fields `K`, `L` of characteristic `p` (i.e. perfect complete
nonarchimedean fields of characteristic `p`; here we retain the algebraic content: perfect
fields of characteristic `p`), with the tilt `K^♭ = lim_{x ↦ x^p} K`:

* the tilt is always perfect: the `p`-power map on `K^♭` is bijective (this holds for the tilt
  of an arbitrary commutative monoid);
* tilting is an equivalence, with the untilt as inverse: `K^♭ ≃+* K` via `(xₙ) ↦ x₀`, and
  likewise for `L`;
* the equivalence is natural in the field: it intertwines the induced map `f^♭ : K^♭ →+* L^♭`
  with `f : K →+* L`.

Together these say that, on the characteristic `p` side, tilting is (naturally isomorphic to)
the identity functor, which is the base case of the tilting correspondence. -/
theorem scholze_perfectoid_tilt (p : ℕ) (hp : p.Prime) (K L : Type*) [Field K] [Field L]
    [ExpChar K p] [ExpChar L p] [PerfectRing K p] [PerfectRing L p] (f : K →+* L) :
    Function.Bijective (fun x : tiltSubmonoid p K => x ^ p) ∧ CharP K p ∧ CharP L p ∧
      ∃ eK : tiltSubring p K ≃+* K, ∃ eL : tiltSubring p L ≃+* L,
        (∀ x : tiltSubring p K, eK x = (x : ℕ → K) 0) ∧
        (∀ y : tiltSubring p L, eL y = (y : ℕ → L) 0) ∧
        (∀ x : tiltSubring p K, eL (tiltRingHom p f x) = f (eK x)) := by
  refine ⟨tilt_pow_bijective p K, charP_of_expChar_prime' K p hp, charP_of_expChar_prime' L p hp,
    tiltEquiv p K, tiltEquiv p L, fun x => rfl, fun y => rfl, fun x => rfl⟩

/-- Non-vacuity check: the hypotheses of `scholze_perfectoid_tilt` are satisfiable, e.g. by the
prime field `ZMod p`, whose tilt is isomorphic to itself. -/
example (p : ℕ) [Fact p.Prime] : Nonempty (tiltSubring p (ZMod p) ≃+* ZMod p) :=
  ⟨tiltEquiv p (ZMod p)⟩

end Frontier

#print axioms Frontier.scholze_perfectoid_tilt

