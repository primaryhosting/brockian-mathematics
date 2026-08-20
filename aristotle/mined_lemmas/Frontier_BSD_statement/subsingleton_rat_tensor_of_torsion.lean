import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
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

namespace Frontier

open Filter Topology WeierstrassCurve

/-!
## Setup

An elliptic curve over `ℚ` is presented by an integral Weierstrass model `W : WeierstrassCurve ℤ`
with nonvanishing discriminant.  We formalize:

* the *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`;
* the local data (`a_p`, `ε_p`) and the Euler factors of the Hasse–Weil `L`-function of `W`;
* the predicate `IsHasseWeilLFunction W L` saying that the entire function `L` is the analytic
  continuation of the Hasse–Weil `L`-series of `W`;
* the Birch–Swinnerton-Dyer equality `ord_{s=1} L(E, s) = rank E(ℚ)`.
-/

/-- The Mordell–Weil group `E(ℚ)` of the Weierstrass model `W` over `ℤ`, namely the group of
nonsingular rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`, defined as the
dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

theorem subsingleton_rat_tensor_of_torsion (M : Type*) [AddCommGroup M]
    (htor : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m = 0) :
    Subsingleton (TensorProduct ℤ ℚ M) := by
  have h : ∀ z : TensorProduct ℤ ℚ M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        obtain ⟨n, hn, hnm'⟩ := htor m
        have hnm : ((n : ℤ)) • m = 0 := by
          rw [Nat.cast_smul_eq_nsmul ℤ]; exact hnm'
        have hcard : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        have hq : q = ((n : ℤ)) • (q / (n : ℚ)) := by
          rw [zsmul_eq_mul]
          push_cast
          field_simp
        rw [hq, TensorProduct.smul_tmul, hnm, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

/-- If the Mordell–Weil group `E(ℚ)` is a torsion group, then the algebraic rank of `E` is `0`. -/
