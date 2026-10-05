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
