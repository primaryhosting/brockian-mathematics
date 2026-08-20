/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to come first in a file, so the module docstring version of
-- the header above is repeated immediately after the imports.)

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open NumberField

/-- A cyclotomic extension of `ℚ` is Galois. -/
theorem isGalois_cyclotomic (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] : IsGalois ℚ K :=
  IsCyclotomicExtension.isGalois {n} ℚ K

/-- `ℤ` is the ring of invariants of the action of `Aut(𝓞 K / ℤ)` on `𝓞 K`, for `K` a cyclotomic
field. -/
theorem isInvariant_cyclotomic (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) (𝓞 K ≃ₐ[ℤ] 𝓞 K) :=
  have := isGalois_cyclotomic n K
  Algebra.isInvariant_of_isGalois' ℤ ℚ K (𝓞 K)

/-- Two automorphisms of the ring of integers of a cyclotomic field `ℚ(ζₙ)` that agree on a
primitive `n`-th root of unity are equal. -/
theorem aut_ext_of_primitiveRoot (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (σ τ : 𝓞 K ≃ₐ[ℤ] 𝓞 K) (h : σ hζ.toInteger = τ hζ.toInteger) : σ = τ := by
  obtain ⟨f, rfl⟩ := (galRestrict ℤ ℚ K (𝓞 K)).surjective σ
  obtain ⟨g, rfl⟩ := (galRestrict ℤ ℚ K (𝓞 K)).surjective τ
  have hf : f ζ = g ζ := by
    have := congrArg (algebraMap (𝓞 K) K) h
    rwa [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply,
      show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from rfl] at this
  have hfg : f = g := by
    apply AlgEquiv.coe_algHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    simpa [IsPrimitiveRoot.powerBasis_gen] using hf
  rw [hfg]

/-- If two automorphisms of `𝓞 ℚ(ζₙ)` send a primitive `n`-th root of unity `z` to `z ^ i` and
`z ^ j` respectively, with `i ≡ j (mod n)`, then they are equal. -/
theorem aut_eq_of_pow_congr (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (σ τ : 𝓞 K ≃ₐ[ℤ] 𝓞 K) {i j : ℕ}
    (hi : σ hζ.toInteger = hζ.toInteger ^ i) (hj : τ hζ.toInteger = hζ.toInteger ^ j)
    (hij : (i : ZMod n) = (j : ZMod n)) : σ = τ := by
  have hz : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  have key : ∀ m : ℕ, hζ.toInteger ^ m = hζ.toInteger ^ (m % n) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hz.pow_eq_one, one_pow, one_mul]
  refine aut_ext_of_primitiveRoot n K hζ σ τ ?_
  rw [hi, hj, key i, key j, (ZMod.natCast_eq_natCast_iff _ _ _).mp hij]

/-- **Chebotarev density theorem** (cyclotomic case, in the qualitative "infinitely many primes"
form).

Let `K = ℚ(ζₙ)` be a cyclotomic field and let `σ` be any element of its Galois group,
realized as `Aut(𝓞 K / ℤ) ≃ Gal(K/ℚ)`.  Then there are infinitely many rational primes `p`
admitting a prime ideal `Q` of `𝓞 K` lying over `p` (i.e. `Q ∩ ℤ = pℤ`) whose Frobenius element
is `σ`, i.e. `σ x ≡ x ^ p (mod Q)` for all `x ∈ 𝓞 K`.

Since the Galois group of a cyclotomic field is abelian, the conjugacy class of `σ` is `{σ}`, so
this says precisely that every Frobenius conjugacy class of `Gal(ℚ(ζₙ)/ℚ)` is the Frobenius class
of infinitely many primes.  The proof deduces this from Dirichlet's theorem on primes in
arithmetic progressions, via the identification of the Frobenius at `p` with `ζ ↦ ζ ^ p`. -/
theorem chebotarev (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (σ : 𝓞 K ≃ₐ[ℤ] 𝓞 K) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  haveI := isInvariant_cyclotomic n K
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ n := ⟨_, IsCyclotomicExtension.zeta_spec n ℚ K⟩
  have hz : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  -- `a` is the element of `(ZMod n)ˣ` corresponding to `σ` under `Gal(K/ℚ) ≃ (ZMod n)ˣ`.
  set a : (ZMod n)ˣ := hz.autToPow ℤ σ with ha
  have hσz : σ hζ.toInteger = hζ.toInteger ^ ((a : ZMod n)).val := (hz.autToPow_spec ℤ σ).symm
  -- By Dirichlet's theorem there are infinitely many primes `p` with `p ≡ a (mod n)`.
  refine Set.Infinite.mono ?_
    (Nat.infinite_setOf_prime_and_eq_mod (q := n) (a := (a : ZMod n)) a.isUnit)
  rintro p ⟨hp, hpa⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hPprime : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  -- Choose a prime `Q` of `𝓞 K` above `p`.
  obtain ⟨Q, -, hQp, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K))
    (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
        exact bot_le)
  haveI : Q.IsPrime := hQp
  have hQunder : Q.under ℤ = Ideal.span {(p : ℤ)} := hQu
  have hpQ : (algebraMap ℤ (𝓞 K)) (p : ℤ) ∈ Q := by
    have : (p : ℤ) ∈ Q.under ℤ := by rw [hQunder]; exact Ideal.mem_span_singleton_self _
    exact this
  have hQbot : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    have h0 : ((p : ℤ)) = 0 := (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)) (by simpa using hpQ)
    exact hp.ne_zero (by exact_mod_cast h0)
  haveI : Q.IsMaximal := hQp.isMaximal hQbot
  -- The residue field of `ℤ` at `Q ∩ ℤ = pℤ` has `p` elements.
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [hQunder, Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  -- A Frobenius element at `Q` exists.
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (𝓞 K ≃ₐ[ℤ] 𝓞 K) Q
  refine ⟨Q, hQp, hQunder, ?_⟩
  -- Since `p ≡ a (mod n)` is a unit, `p` does not divide `n`.
  have hnQ : ((n : ℕ) : 𝓞 K) ∉ Q := by
    intro hmem
    have h1 : ((n : ℕ) : ℤ) ∈ Q.under ℤ := by
      show ((n : ℕ) : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) Q
      simpa using hmem
    rw [hQunder, Ideal.mem_span_singleton] at h1
    have hpn : p ∣ n := by exact_mod_cast h1
    have hu : IsUnit ((p : ZMod n)) := hpa ▸ a.isUnit
    have h2 := hu.map (ZMod.castHom hpn (ZMod p))
    rw [map_natCast] at h2
    simp at h2
  -- Hence the Frobenius at `Q` acts on roots of unity by `z ↦ z ^ p`, as does `σ`.
  have hτz : τ hζ.toInteger = hζ.toInteger ^ p := by
    have := hτ.apply_of_pow_eq_one (ζ := hζ.toInteger) (m := n) hz.pow_eq_one hnQ
    rw [hcard] at this
    simpa using this
  have hst : σ = τ :=
    aut_eq_of_pow_congr n K hζ σ τ hσz hτz (by rw [ZMod.natCast_val, ZMod.cast_id, hpa])
  rw [hst]
  exact hτ

/-- The Chebotarev density theorem above, instantiated at the cyclotomic field `ℚ(ζₙ)` itself;
this witnesses that the hypotheses of `Math2.chebotarev` are satisfiable. -/
theorem chebotarev_cyclotomicField (n : ℕ) [NeZero n]
    (σ : 𝓞 (CyclotomicField n ℚ) ≃ₐ[ℤ] 𝓞 (CyclotomicField n ℚ)) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 (CyclotomicField n ℚ)), Q.IsPrime ∧
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite :=
  chebotarev n (CyclotomicField n ℚ) σ

end Math2

