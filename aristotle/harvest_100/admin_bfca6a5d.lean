/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NumberField IsCyclotomicExtension

namespace Math2

section Auxiliary

/-- In a Galois number field `L`, the elements of the ring of integers fixed by the whole
Galois group are exactly the (images of the) rational integers. -/
instance isInvariant_ringOfIntegers (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L] : Algebra.IsInvariant ℤ (𝓞 L) (L ≃ₐ[ℚ] L) := by
  constructor
  intro x hx
  have hfix : ∀ g : L ≃ₐ[ℚ] L, g (x : L) = (x : L) := fun g =>
    congrArg (fun y : 𝓞 L => (y : L)) (hx g)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (E := L) (x : L)).2 hfix
  have hint : IsIntegral ℤ a := by
    have hxint : IsIntegral ℤ (x : L) := x.2
    rw [← ha] at hxint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ L).injective).1 hxint
  obtain ⟨m, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨m, Subtype.ext ?_⟩
  show (algebraMap ℤ (𝓞 L) m : L) = (x : L)
  rw [← ha]
  simp

/-- Every rational prime lies under some prime ideal of the ring of integers. -/
theorem exists_prime_over (L : Type*) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} := by
  have hprime : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.1 hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 hprime
  obtain ⟨Q, -, hQ1, hQ2⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 L) (Ideal.span {(p : ℤ)}) ⊥
      (by
        intro x hx
        have hx0 : algebraMap ℤ (𝓞 L) x = 0 := by simpa [Ideal.mem_comap] using hx
        have : x = 0 := FaithfulSMul.algebraMap_injective ℤ (𝓞 L) (by simpa using hx0)
        simp [this])
  exact ⟨Q, hQ1, hQ2⟩

/-- The residue ring of `ℤ` at `p` has `p` elements. -/
theorem card_quotient_span (p : ℕ) :
    Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  have h : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = Nat.card (ZMod (p : ℤ).natAbs) :=
    Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv
  rw [h]
  simp [Nat.card_zmod]

end Auxiliary

/-- If the residue of a prime `p` modulo `n` corresponds to `σ` under the embedding of the
Galois group of `L = ℚ(ζₙ)` into `(ZMod n)ˣ`, then any Frobenius element at a prime of `𝓞 L`
above `p` is equal to `σ`. -/
theorem eq_of_isArithFrobAt (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsCyclotomicExtension {n} ℚ L]
    {σ τ : L ≃ₐ[ℚ] L} {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 L)}
    (hQ : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) (hτ : IsArithFrobAt ℤ τ Q)
    (hσ : ((p : ZMod n)) = ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)) :
    τ = σ := by
  have hζ : IsPrimitiveRoot (zeta n ℚ L) n := zeta_spec n ℚ L
  -- `ζ` as an algebraic integer
  have hζIcoe : (hζ.toInteger : L) = zeta n ℚ L := rfl
  have hpow : hζ.toInteger ^ n = 1 := by
    apply Subtype.ext
    push_cast [hζIcoe]
    exact hζ.pow_eq_one
  -- `n ∉ Q`
  have hcop : Nat.Coprime p n := by
    have : IsUnit ((p : ZMod n)) := hσ ▸ Units.isUnit _
    exact (ZMod.isUnit_iff_coprime p n).1 this
  have hnQ : ((n : ℕ) : 𝓞 L) ∉ Q := by
    intro hmem
    have hn : ((n : ℤ)) ∈ Ideal.under ℤ Q := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    rw [hQ, Ideal.mem_span_singleton] at hn
    have hdvd : (p : ℕ) ∣ n := by exact_mod_cast hn
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  -- the Frobenius raises roots of unity to the `p`-th power
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQ]; exact card_quotient_span p
  have hfrob := hτ.apply_of_pow_eq_one hpow hnQ
  rw [hcard] at hfrob
  have hτζ : τ (zeta n ℚ L) = (zeta n ℚ L) ^ p := by
    have := congrArg (fun y : 𝓞 L => (y : L)) hfrob
    simpa [hζIcoe] using this
  -- identify `τ` and `σ` through `autToPow`
  have hspec := hζ.autToPow_spec ℚ τ
  rw [hτζ] at hspec
  have hmodeq : ((hζ.autToPow ℚ τ : ZMod n)).val ≡ p [MOD n] := by
    have hord : orderOf (zeta n ℚ L) = n := hζ.eq_orderOf.symm
    have hfin : IsOfFinOrder (zeta n ℚ L) :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨n, NeZero.pos n, hζ.pow_eq_one⟩
    have h := hfin.pow_eq_pow_iff_modEq.1 hspec
    rwa [hord] at h
  have hcast : ((hζ.autToPow ℚ τ : ZMod n)) = ((p : ZMod n)) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodeq
    simpa [ZMod.natCast_val, ZMod.cast_id] using this
  have hunits : hζ.autToPow ℚ τ = hζ.autToPow ℚ σ := Units.ext (by rw [hcast, hσ])
  exact hζ.autToPow_injective ℚ hunits

/-- **Chebotarev density theorem** for the cyclotomic field `L = ℚ(ζₙ)`, in the following form:
for every element `σ` of the Galois group of `L/ℚ` there are infinitely many rational primes
`p` admitting a prime `Q` of the ring of integers of `L` above `p` at which `σ` is the
(arithmetic) Frobenius element, i.e. `σ x ≡ x ^ p (mod Q)` for every algebraic integer `x`
of `L`. Since the extension is abelian, the Frobenius conjugacy class of such a `p` is exactly
the singleton `{σ}`. -/
theorem chebotarev (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsCyclotomicExtension {n} ℚ L] (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧
      Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have hζ : IsPrimitiveRoot (zeta n ℚ L) n := zeta_spec n ℚ L
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_eq_mod (q := n)
    (a := ((hζ.autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)) (Units.isUnit _))
  rintro p ⟨hp, hpu⟩
  refine ⟨hp, ?_⟩
  obtain ⟨Q, hQprime, hQunder⟩ := exists_prime_over L hp
  haveI : Q.IsPrime := hQprime
  have hQbot : Q ≠ ⊥ := by
    intro h
    have hmem : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQunder]; exact Ideal.mem_span_singleton_self _
    rw [h] at hmem
    have hz : ((p : ℤ)) = 0 := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    exact hp.ne_zero (by exact_mod_cast hz)
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (L ≃ₐ[ℚ] L) Q
  have hτσ : τ = σ := eq_of_isArithFrobAt n L hp hQunder hτ hpu
  exact ⟨Q, hQprime, hQunder, hτσ ▸ hτ⟩

/-- A variant of `Math2.chebotarev` phrased with Mathlib's canonical Frobenius element
`arithFrobAt`: for every element `σ` of the Galois group of `L = ℚ(ζₙ)` over `ℚ` there are
infinitely many rational primes `p` having a prime `Q` of `𝓞 L` above them whose Frobenius
element is exactly `σ`. (As `L/ℚ` is abelian, the Frobenius conjugacy class attached to such
a prime `p` is the singleton `{σ}`.) -/
theorem chebotarev_arithFrobAt (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsCyclotomicExtension {n} ℚ L] [IsGalois ℚ L] (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ ∃ (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime) (hf : Finite (𝓞 L ⧸ Q)),
      Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
        letI := hQ; letI := hf; arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = σ}.Infinite := by
  have hζ : IsPrimitiveRoot (zeta n ℚ L) n := zeta_spec n ℚ L
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_eq_mod (q := n)
    (a := ((hζ.autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)) (Units.isUnit _))
  rintro p ⟨hp, hpu⟩
  refine ⟨hp, ?_⟩
  obtain ⟨Q, hQprime, hQunder⟩ := exists_prime_over L hp
  haveI : Q.IsPrime := hQprime
  have hQbot : Q ≠ ⊥ := by
    intro h
    have hmem : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQunder]; exact Ideal.mem_span_singleton_self _
    rw [h] at hmem
    have hz : ((p : ℤ)) = 0 := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    exact hp.ne_zero (by exact_mod_cast hz)
  haveI hfin : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  exact ⟨Q, hQprime, hfin, hQunder,
    eq_of_isArithFrobAt n L hp hQunder (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) hpu⟩

end Math2

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

