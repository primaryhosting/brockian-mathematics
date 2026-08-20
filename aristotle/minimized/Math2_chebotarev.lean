import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires `import` to be the very first command of a file, so the
header comment above is placed immediately after the single `import Mathlib` line.

# Chebotarev density theorem for Frobenius conjugacy classes

We prove the Chebotarev density theorem, in its "infinitude" form, for cyclotomic extensions of
`ℚ`: if `K = ℚ(ζₙ)` and `σ ∈ Gal(K/ℚ)`, then there are infinitely many rational primes `p`
admitting a prime `Q` of `𝓞 K` above `p` at which `σ` is an arithmetic Frobenius element, i.e.
`σ • x ≡ x ^ #(ℤ/(p)) (mod Q)` for all `x ∈ 𝓞 K` (Mathlib's `IsArithFrobAt`).  Since `Gal(K/ℚ)` is
abelian in this case, the conjugacy class of `σ` is `{σ}`, so this says precisely that every
Frobenius conjugacy class is hit by infinitely many primes.

The two main external inputs are:
* `Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet's theorem on primes in arithmetic
  progressions), which is the analytic input, and
* `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top` (`𝓞 ℚ(ζₙ) = ℤ[ζₙ]`), which lets us identify
  the Galois action modulo `Q` with the `p`-th power map.
-/

open NumberField IsCyclotomicExtension

namespace Math2

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The `p`-th power map on the residue ring `𝓞 K ⧸ Q`, precomposed with the reduction map,
as a `ℤ`-algebra map `𝓞 K → 𝓞 K ⧸ Q`. It is a ring homomorphism because `𝓞 K ⧸ Q` has
characteristic `p`. -/

noncomputable def powFrobHom (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hpQ : (p : 𝓞 K) ∈ Q) : 𝓞 K →ₐ[ℤ] (𝓞 K ⧸ Q) :=
  haveI : CharP (𝓞 K ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa using (Ideal.Quotient.eq_zero_iff_mem).2 hpQ)
  haveI : ExpChar (𝓞 K ⧸ Q) p := ExpChar.prime hp
  ((frobenius (𝓞 K ⧸ Q) p).comp (Ideal.Quotient.mk Q)).toIntAlgHom

/-- The action of `σ : Gal(K/ℚ)` on `𝓞 K`, followed by reduction mod `Q`, as a `ℤ`-algebra map. -/

noncomputable def galQuotHom (σ : Gal(K/ℚ)) (Q : Ideal (𝓞 K)) : 𝓞 K →ₐ[ℤ] (𝓞 K ⧸ Q) :=
  ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ)).toIntAlgHom

omit [NumberField K] [IsCyclotomicExtension {n} ℚ K] in

lemma powFrobHom_apply (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hpQ : (p : 𝓞 K) ∈ Q) (x : 𝓞 K) :
    powFrobHom p hp Q hpQ x = Ideal.Quotient.mk Q (x ^ p) := by
  simp [powFrobHom, frobenius_def]

omit [IsCyclotomicExtension {n} ℚ K] in

lemma galQuotHom_apply (σ : Gal(K/ℚ)) (Q : Ideal (𝓞 K)) (x : 𝓞 K) :
    galQuotHom σ Q x = Ideal.Quotient.mk Q (σ • x) := rfl

/-- If `p` is a prime whose class mod `n` is the class attached to `σ` by
`IsCyclotomicExtension.Rat.galEquivZMod`, and `Q` is a prime of `𝓞 K` above `p`, then `σ` acts as
the `p`-th power map modulo `Q`. -/

theorem smul_sub_pow_mem (σ : Gal(K/ℚ)) {p : ℕ} (hp : p.Prime)
    (hpa : (p : ZMod n) = (Rat.galEquivZMod n K σ : ZMod n))
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hpQ : (p : 𝓞 K) ∈ Q) (x : 𝓞 K) :
    σ • x - x ^ p ∈ Q := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have key : galQuotHom σ Q = powFrobHom p hp Q hpQ := by
    refine AlgHom.ext_of_adjoin_eq_top (Rat.adjoin_singleton_eq_top hζ) ?_
    rintro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    rw [galQuotHom_apply, powFrobHom_apply,
      Rat.galEquivZMod_smul_of_pow_eq n K σ hζ.toInteger_isPrimitiveRoot.pow_eq_one]
    congr 1
    have hord : orderOf hζ.toInteger = n := (hζ.toInteger_isPrimitiveRoot.eq_orderOf).symm
    rw [(hζ.toInteger_isPrimitiveRoot.isOfFinOrder (NeZero.ne n)).pow_inj_mod, hord]
    have hcast : (((Rat.galEquivZMod n K σ : ZMod n).val : ℕ) : ZMod n) = (p : ZMod n) := by
      rw [hpa, ZMod.natCast_val, ZMod.cast_id]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
  have h2 := congrArg (fun f => f x) key
  simp only [powFrobHom_apply] at h2
  exact (Ideal.Quotient.eq).1 h2

/-- **Chebotarev density theorem** (infinitude form) for the cyclotomic extension `K = ℚ(ζₙ)` of
`ℚ`: every element `σ` of `Gal(K/ℚ)` is an arithmetic Frobenius element at infinitely many
primes.  Precisely, for infinitely many rational primes `p` there is a prime `Q` of the ring of
integers `𝓞 K` lying over `p` such that `σ` is an arithmetic Frobenius at `Q`, i.e.
`σ • x ≡ x ^ #(ℤ/(p)) (mod Q)` for all `x ∈ 𝓞 K`.

As `Gal(ℚ(ζₙ)/ℚ)` is abelian, the conjugacy class of `σ` is `{σ}`, so this is exactly the
statement that each Frobenius conjugacy class occurs for infinitely many primes. -/

theorem chebotarev (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (σ : Gal(K/ℚ)) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧
      Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  refine (Nat.infinite_setOf_prime_and_eq_mod
    (q := n) (a := ((Rat.galEquivZMod n K σ : (ZMod n)ˣ) : ZMod n)) (Units.isUnit _)).mono ?_
  rintro p ⟨hp, hpa⟩
  refine ⟨hp, ?_⟩
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  have hbot : Ideal.comap (algebraMap ℤ (𝓞 K)) ⊥ ≤ Ideal.span {(p : ℤ)} := by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
    exact bot_le
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) hbot
  have hQc' : Ideal.under ℤ Q = Ideal.span {(p : ℤ)} := hQc
  refine ⟨Q, hQp, hQc', ?_⟩
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have h1 : (p : ℤ) ∈ Ideal.under ℤ Q := by rw [hQc']; exact Ideal.subset_span rfl
    simpa using h1
  intro x
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQc', Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv, Nat.card_zmod]
    simp
  rw [hcard]
  exact smul_sub_pow_mem σ hp hpa Q hpQ x

/-- The hypotheses of `Math2.chebotarev` are satisfiable: the statement applied to the concrete
cyclotomic field `CyclotomicField n ℚ`. -/
