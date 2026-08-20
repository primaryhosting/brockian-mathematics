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

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem exists_residue_isFrobeniusAt (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    ∃ a : ZMod q, IsUnit a ∧ ∀ n : ℕ, IsFrobeniusAt q n σ ↔ (n : ZMod q) = a := by
  have hq : 0 < q := Nat.pos_of_neZero q
  set L := CyclotomicField q ℚ
  set z := IsCyclotomicExtension.zeta q ℚ L with hzdef
  have hz : IsPrimitiveRoot z q := IsCyclotomicExtension.zeta_spec q ℚ L
  set u : (ZMod q)ˣ := hz.autToPow ℚ σ with hu
  have hspec : z ^ ((u : ZMod q)).val = σ z := hz.autToPow_spec ℚ σ
  have hzq : z ^ q = 1 := hz.pow_eq_one
  refine ⟨(u : ZMod q), u.isUnit, fun n => ?_⟩
  constructor
  · intro hf
    have h1 : z ^ ((u : ZMod q)).val = z ^ n := hspec.trans (hf z hzq)
    rw [pow_mod_of_pow_eq_one hzq ((u : ZMod q)).val, pow_mod_of_pow_eq_one hzq n] at h1
    have h2 := hz.pow_inj (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) h1
    have h3 : n ≡ ((u : ZMod q)).val [MOD q] := h2.symm
    rw [← ZMod.natCast_eq_natCast_iff] at h3
    rw [h3, ZMod.natCast_zmod_val]
  · intro hn x hx
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hx
    have hnu : ((u : ZMod q)).val ≡ n [MOD q] := by
      have h : ((n : ZMod q)) = ((((u : ZMod q)).val : ℕ) : ZMod q) := by
        rw [hn, ZMod.natCast_zmod_val]
      exact (ZMod.natCast_eq_natCast_iff _ _ _ |>.mp h).symm
    have hmod : ((u : ZMod q)).val * i % q = i * n % q := by
      calc ((u : ZMod q)).val * i % q = n * i % q := hnu.mul_right i
        _ = i * n % q := by rw [mul_comm]
    rw [map_pow, ← hspec, ← pow_mul, ← pow_mul,
      pow_mod_of_pow_eq_one hzq (((u : ZMod q)).val * i), pow_mod_of_pow_eq_one hzq (i * n), hmod]

/-- The Galois group of a cyclotomic extension is abelian, so conjugacy classes are singletons. -/
