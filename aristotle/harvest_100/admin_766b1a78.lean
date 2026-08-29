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

/-
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/
noncomputable def QtBot (b : Submodule k M) : Qt ⊥ b ≃ₗ[k] b :=
  (Submodule.quotEquivOfEqBot _ (by simp [Submodule.submoduleOf])).symm.symm

/-- `⊤ / a ≃ M / a`. -/
noncomputable def QtTop (a : Submodule k M) : Qt a (⊤ : Submodule k M) ≃ₗ[k] M ⧸ a :=
  Submodule.Quotient.equiv _ _ Submodule.topEquiv (by
    ext x
    simp [Submodule.submoduleOf])

/-- Transport of the quotient `b / a` along a linear automorphism. -/
noncomputable def QtCongr {a b a' b' : Submodule k M} (hab : a ≤ b) (e : M ≃ₗ[k] M)
    (ha : a.map (e : M →ₗ[k] M) = a') (hb : b.map (e : M →ₗ[k] M) = b') :
    Qt a b ≃ₗ[k] Qt a' b' := by
  set E : b ≃ₗ[k] b' := (e.submoduleMap b).trans (LinearEquiv.ofEq _ _ hb) with hE
  have hEc : ∀ x : b, ((E x : b') : M) = e (x : M) := fun x => rfl
  refine Submodule.Quotient.equiv _ _ E ?_
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    show ((E x : b') : M) ∈ a'
    rw [hEc, ← ha]
    exact ⟨(x : M), hx, rfl⟩
  · intro y hy
    have hy' : ((y : b') : M) ∈ a' := hy
    rw [← ha] at hy'
    obtain ⟨z, hz, hze⟩ := hy'
    refine ⟨⟨z, hab hz⟩, hz, ?_⟩
    apply Subtype.ext
    exact hze

/-- The canonical injection `b / a → c / a` for `a ≤ b ≤ c`. -/
noncomputable def QtIncl {a b c : Submodule k M} (_hab : a ≤ b) (hbc : b ≤ c) :
    Qt a b →ₗ[k] Qt a c :=
  Submodule.mapQ _ _ (Submodule.inclusion hbc) (by
    intro x hx
    simpa [Submodule.submoduleOf, Submodule.inclusion] using hx)

/-- The canonical surjection `c / a → c / b` for `a ≤ b ≤ c`. -/
noncomputable def QtProj {a b c : Submodule k M} (hab : a ≤ b) :
    Qt a c →ₗ[k] Qt b c :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    exact hab hx)

lemma QtIncl_apply {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c) (x : b) :
    QtIncl hab hbc (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion hbc x) := rfl

lemma QtIncl_injective {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c) :
    Function.Injective (QtIncl hab hbc) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y
  refine Submodule.Quotient.induction_on _ y ?_
  intro x hx
  rw [LinearMap.mem_ker, QtIncl_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  simpa [Submodule.submoduleOf, Submodule.inclusion] using hx

lemma QtProj_surjective {a b c : Submodule k M} (hab : a ≤ b) :
    Function.Surjective (QtProj (c := c) hab) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩

lemma QtProj_ker {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c) :
    LinearMap.ker (QtProj (c := c) hab) = LinearMap.range (QtIncl hab hbc) := by
  apply le_antisymm
  · rw [SetLike.le_def]
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro x hx
    have hx' : x ∈ b.submoduleOf c := by
      rw [LinearMap.mem_ker] at hx
      rwa [show (QtProj (c := c) hab) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x from rfl,
        Submodule.Quotient.mk_eq_zero] at hx
    have hxb : (x : M) ∈ b := hx'
    exact ⟨Submodule.Quotient.mk ⟨(x : M), hxb⟩, rfl⟩
  · rintro y ⟨z, rfl⟩
    refine Submodule.Quotient.induction_on _ z ?_
    intro w
    rw [LinearMap.mem_ker, QtIncl_apply,
      show (QtProj (c := c) hab) (Submodule.Quotient.mk (Submodule.inclusion hbc w))
        = Submodule.Quotient.mk (Submodule.inclusion hbc w) from rfl,
      Submodule.Quotient.mk_eq_zero]
    exact w.2

/-- Rank additivity along a chain `a ≤ b ≤ c`. -/
lemma rank_Qt_add {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c) :
    Module.rank k (Qt a b) + Module.rank k (Qt b c) = Module.rank k (Qt a c) := by
  have h1 : Module.rank k (LinearMap.range (QtProj (c := c) hab))
      + Module.rank k (LinearMap.ker (QtProj (c := c) hab)) = Module.rank k (Qt a c) :=
    LinearMap.rank_range_add_rank_ker _
  have h2 : Module.rank k (LinearMap.range (QtProj (c := c) hab)) = Module.rank k (Qt b c) := by
    have : LinearMap.range (QtProj (c := c) hab) = ⊤ :=
      LinearMap.range_eq_top.2 (QtProj_surjective hab)
    rw [this]
    exact (Submodule.topEquiv (R := k) (M := Qt b c)).rank_eq
  have h3 : Module.rank k (LinearMap.ker (QtProj (c := c) hab)) = Module.rank k (Qt a b) := by
    rw [QtProj_ker hab hbc]
    exact ((LinearEquiv.ofInjective _ (QtIncl_injective hab hbc)).rank_eq).symm
  rw [h2, h3] at h1
  rw [← h1]
  exact add_comm _ _

lemma finrank_Qt_add {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c)
    [Module.Finite k (Qt a b)] [Module.Finite k (Qt b c)] :
    Module.finrank k (Qt a b) + Module.finrank k (Qt b c) = Module.finrank k (Qt a c) := by
  have h := rank_Qt_add hab hbc
  have e1 : Module.rank k (Qt a b) = (Module.finrank k (Qt a b) : Cardinal) :=
    (Module.finrank_eq_rank k _).symm
  have e2 : Module.rank k (Qt b c) = (Module.finrank k (Qt b c) : Cardinal) :=
    (Module.finrank_eq_rank k _).symm
  rw [e1, e2] at h
  have hc : Module.rank k (Qt a c) = ((Module.finrank k (Qt a b) + Module.finrank k (Qt b c) : ℕ) :
      Cardinal) := by
    rw [← h]; push_cast; ring
  have h4 : Module.finrank k (Qt a c) = Cardinal.toNat (Module.rank k (Qt a c)) := rfl
  rw [h4, hc, Cardinal.toNat_natCast]

lemma finite_Qt_of_chain {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c)
    [Module.Finite k (Qt a c)] : Module.Finite k (Qt a b) ∧ Module.Finite k (Qt b c) := by
  constructor
  · exact Module.Finite.of_injective (QtIncl hab hbc) (QtIncl_injective hab hbc)
  · exact Module.Finite.of_surjective (QtProj (c := c) hab) (QtProj_surjective hab)

lemma finite_Qt_of_both {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c)
    [Module.Finite k (Qt a b)] [Module.Finite k (Qt b c)] : Module.Finite k (Qt a c) := by
  have h := rank_Qt_add hab hbc
  have h1 : Module.rank k (Qt a b) < Cardinal.aleph0 := Module.rank_lt_aleph0 k _
  have h2 : Module.rank k (Qt b c) < Cardinal.aleph0 := Module.rank_lt_aleph0 k _
  have : Module.rank k (Qt a c) < Cardinal.aleph0 := by
    rw [← h]; exact Cardinal.add_lt_aleph0 h1 h2
  exact Module.rank_lt_aleph0_iff.mp this

end Math2

/-
Basic valuation-theoretic setup for the function field of a smooth projective curve.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open scoped Classical

/-- Valuation data on a field `K` over a base field `k`, indexed by a type `Place`
of closed points. Each place carries a normalized discrete valuation of `K`
which is trivial on `k`. -/
structure PlaceData (k K : Type*) [Field k] [Field K] [Algebra k K] (Place : Type*) where
  /-- The order of vanishing of `x` at the place `P` (junk value `0` at `x = 0`). -/
  v : Place → K → ℤ
  v_zero : ∀ P, v P 0 = 0
  v_mul : ∀ (P : Place) {x y : K}, x ≠ 0 → y ≠ 0 → v P (x * y) = v P x + v P y
  v_add : ∀ (P : Place) {x y : K}, x + y ≠ 0 → min (v P x) (v P y) ≤ v P (x + y)
  v_algebraMap : ∀ (P : Place) (c : k), v P (algebraMap k K c) = 0
  exists_uniformizer : ∀ P : Place, ∃ t : K, t ≠ 0 ∧ v P t = 1
  v_finite_support : ∀ {x : K}, x ≠ 0 → {P | v P x ≠ 0}.Finite

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)

lemma v_one (P : Place) : V.v P 1 = 0 := by
  have := V.v_algebraMap P 1
  simpa using this

lemma v_neg (P : Place) (x : K) : V.v P (-x) = V.v P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : (-x) = (algebraMap k K (-1)) * x := by simp
    rw [h, V.v_mul P (by simp) hx, V.v_algebraMap]
    ring

lemma v_inv (P : Place) {x : K} (hx : x ≠ 0) : V.v P x⁻¹ = - V.v P x := by
  have h := V.v_mul P (x := x) (y := x⁻¹) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, V.v_one] at h
  omega

/-- The order of vanishing, with value `⊤` at `0`. -/
noncomputable def ord (P : Place) (x : K) : WithTop ℤ :=
  if x = 0 then ⊤ else (V.v P x : WithTop ℤ)

@[simp] lemma ord_zero (P : Place) : V.ord P 0 = ⊤ := by simp [ord]

lemma ord_of_ne (P : Place) {x : K} (hx : x ≠ 0) : V.ord P x = (V.v P x : WithTop ℤ) := by
  simp [ord, hx]

lemma ord_eq_top_iff (P : Place) (x : K) : V.ord P x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [V.ord_of_ne P hx] at h
    exact (WithTop.coe_ne_top h)
  · rintro rfl; simp

lemma ord_mul (P : Place) (x y : K) : V.ord P (x * y) = V.ord P x + V.ord P y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [V.ord_of_ne P hx, V.ord_of_ne P hy, V.ord_of_ne P (mul_ne_zero hx hy), V.v_mul P hx hy]
  rfl

lemma coe_min (a b : ℤ) :
    ((min a b : ℤ) : WithTop ℤ) = min (a : WithTop ℤ) (b : WithTop ℤ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, eq_comm]
    exact min_eq_left (by exact_mod_cast h)
  · rw [min_eq_right h, eq_comm]
    exact min_eq_right (by exact_mod_cast h)

lemma ord_add (P : Place) (x y : K) : min (V.ord P x) (V.ord P y) ≤ V.ord P (x + y) := by
  rcases eq_or_ne (x + y) 0 with h | h
  · simp [h]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [V.ord_of_ne P hx, V.ord_of_ne P hy, V.ord_of_ne P h, ← coe_min]
  exact_mod_cast V.v_add P (x := x) (y := y) h

lemma ord_algebraMap (P : Place) (c : k) : 0 ≤ V.ord P (algebraMap k K c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [V.ord_of_ne P (by simpa using hc), V.v_algebraMap]
    exact le_rfl

lemma ord_neg (P : Place) (x : K) : V.ord P (-x) = V.ord P x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [V.ord_of_ne P hx, V.ord_of_ne P (neg_ne_zero.2 hx), V.v_neg]

lemma ord_le_ord_smul (P : Place) (c : k) (x : K) : V.ord P x ≤ V.ord P (c • x) := by
  rw [Algebra.smul_def, V.ord_mul]
  have h0 : (0 : WithTop ℤ) ≤ V.ord P (algebraMap k K c) := V.ord_algebraMap P c
  calc V.ord P x = 0 + V.ord P x := by rw [zero_add]
    _ ≤ V.ord P (algebraMap k K c) + V.ord P x := by
        exact add_le_add h0 le_rfl

lemma ord_smul_of_ne (P : Place) {c : k} (hc : c ≠ 0) (x : K) :
    V.ord P (c • x) = V.ord P x := by
  rw [Algebra.smul_def, V.ord_mul, V.ord_of_ne P (by simpa using hc), V.v_algebraMap]
  simp

lemma ord_inv (P : Place) {x : K} (hx : x ≠ 0) :
    V.ord P x⁻¹ = (-(V.v P x) : ℤ) := by
  rw [V.ord_of_ne P (inv_ne_zero hx), V.v_inv P hx]

/-- The `k`-subspace `{x : K | ord_P x ≥ m}`. -/
def Kge (P : Place) (m : ℤ) : Submodule k K where
  carrier := {x : K | (m : WithTop ℤ) ≤ V.ord P x}
  add_mem' := by
    intro a b ha hb
    exact le_trans (le_min ha hb) (V.ord_add P a b)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    exact le_trans ha (V.ord_le_ord_smul P c a)

@[simp] lemma mem_Kge {P : Place} {m : ℤ} {x : K} :
    x ∈ V.Kge P m ↔ (m : WithTop ℤ) ≤ V.ord P x := Iff.rfl

lemma Kge_mono {P : Place} {m n : ℤ} (h : m ≤ n) : V.Kge P n ≤ V.Kge P m := by
  intro x hx
  simp only [mem_Kge] at *
  exact le_trans (by exact_mod_cast h) hx

end PlaceData

end Math2

/-
Divisors, degrees, Riemann-Roch spaces `L(D)`, and the local dimension computation
`dim_k (Kge P m / Kge P n) = (n - m) * deg P`.
-/
import RequestProject.RR.Basic
import RequestProject.RR.Aux

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)

/-! ### Powers and elements of prescribed valuation -/

lemma v_pow (P : Place) {x : K} (hx : x ≠ 0) (n : ℕ) : V.v P (x ^ n) = n * V.v P x := by
  induction n with
  | zero => simpa using V.v_one P
  | succ n ih =>
      rw [pow_succ, V.v_mul P (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

lemma exists_val_eq (P : Place) (m : ℤ) : ∃ u : K, u ≠ 0 ∧ V.v P u = m := by
  obtain ⟨t, ht0, ht⟩ := V.exists_uniformizer P
  rcases le_or_gt 0 m with h | h
  · refine ⟨t ^ m.toNat, pow_ne_zero _ ht0, ?_⟩
    rw [V.v_pow P ht0, ht, mul_one]
    omega
  · refine ⟨(t ^ (-m).toNat)⁻¹, inv_ne_zero (pow_ne_zero _ ht0), ?_⟩
    rw [V.v_inv P (pow_ne_zero _ ht0), V.v_pow P ht0, ht, mul_one]
    omega

/-! ### Multiplication by a nonzero element -/

/-- Multiplication by a nonzero element of `K`, as a `k`-linear automorphism. -/
noncomputable def mulEquiv {u : K} (hu : u ≠ 0) : K ≃ₗ[k] K where
  toFun x := u * x
  map_add' a b := by ring
  map_smul' c a := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    ring
  invFun x := u⁻¹ * x
  left_inv x := by field_simp
  right_inv x := by field_simp

@[simp] lemma mulEquiv_apply {u : K} (hu : u ≠ 0) (x : K) :
    (mulEquiv (k := k) hu) x = u * x := rfl

lemma map_Kge (P : Place) (m : ℤ) {u : K} (hu : u ≠ 0) :
    (V.Kge P m).map ((mulEquiv (k := k) hu : K ≃ₗ[k] K) : K →ₗ[k] K)
      = V.Kge P (m + V.v P u) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simp only [mem_Kge] at hx ⊢
    show ((m + V.v P u : ℤ) : WithTop ℤ) ≤ V.ord P (u * x)
    rw [V.ord_mul, V.ord_of_ne P hu]
    push_cast
    rw [add_comm ((V.v P u : WithTop ℤ)) _]
    exact add_le_add hx le_rfl
  · intro y hy
    simp only [mem_Kge] at hy
    refine ⟨u⁻¹ * y, ?_, ?_⟩
    swap
    · show u * (u⁻¹ * y) = y
      field_simp
    show ((m : ℤ) : WithTop ℤ) ≤ V.ord P (u⁻¹ * y)
    rw [V.ord_mul, V.ord_inv P hu]
    calc ((m : ℤ) : WithTop ℤ)
        = ((-(V.v P u) : ℤ) : WithTop ℤ) + ((m + V.v P u : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          ring
      _ ≤ ((-(V.v P u) : ℤ) : WithTop ℤ) + V.ord P y := add_le_add le_rfl hy

/-! ### The degree of a place -/

/-- The degree of the place `P`: the dimension of its residue field over `k`. -/
noncomputable def degP (P : Place) : ℕ := Module.finrank k (Qt (V.Kge P 1) (V.Kge P 0))

variable (hfin : ∀ P : Place, Module.Finite k (Qt (V.Kge P 1) (V.Kge P 0)))

include hfin

lemma finite_Qt_Kge_succ (P : Place) (m : ℤ) :
    Module.Finite k (Qt (V.Kge P (m + 1)) (V.Kge P m)) := by
  obtain ⟨u, hu, hvu⟩ := V.exists_val_eq P m
  have e : Qt (V.Kge P 1) (V.Kge P 0) ≃ₗ[k] Qt (V.Kge P (m + 1)) (V.Kge P m) := by
    refine QtCongr (V.Kge_mono (by norm_num)) (mulEquiv (k := k) hu) ?_ ?_
    · rw [V.map_Kge P 1 hu, hvu, add_comm]
    · rw [V.map_Kge P 0 hu, hvu, zero_add]
  have := hfin P
  exact Module.Finite.equiv e

lemma finrank_Qt_Kge_succ (P : Place) (m : ℤ) :
    Module.finrank k (Qt (V.Kge P (m + 1)) (V.Kge P m)) = V.degP P := by
  obtain ⟨u, hu, hvu⟩ := V.exists_val_eq P m
  have e : Qt (V.Kge P 1) (V.Kge P 0) ≃ₗ[k] Qt (V.Kge P (m + 1)) (V.Kge P m) := by
    refine QtCongr (V.Kge_mono (by norm_num)) (mulEquiv (k := k) hu) ?_ ?_
    · rw [V.map_Kge P 1 hu, hvu, add_comm]
    · rw [V.map_Kge P 0 hu, hvu, zero_add]
  exact (e.finrank_eq).symm

omit hfin in
lemma subsingleton_Qt_self {M : Type*} [AddCommGroup M] [Module k M] (a : Submodule k M) :
    Subsingleton (Qt a a) := by
  have htop : (a.submoduleOf a) = ⊤ := Submodule.submoduleOf_self a
  constructor
  intro x y
  refine Submodule.Quotient.induction_on _ x fun p => ?_
  refine Submodule.Quotient.induction_on _ y fun q => ?_
  rw [Submodule.Quotient.eq, htop]
  trivial

omit hfin in
lemma finrank_Qt_self {M : Type*} [AddCommGroup M] [Module k M] (a : Submodule k M) :
    Module.finrank k (Qt a a) = 0 := by
  have : Subsingleton (Qt a a) := subsingleton_Qt_self (k := k) a
  exact Module.finrank_zero_of_subsingleton

omit hfin in
lemma finite_Qt_self {M : Type*} [AddCommGroup M] [Module k M] (a : Submodule k M) :
    Module.Finite k (Qt a a) := by
  have : Subsingleton (Qt a a) := subsingleton_Qt_self (k := k) a
  refine ⟨?_⟩
  rw [Subsingleton.elim (⊤ : Submodule k (Qt a a)) ⊥]
  exact Submodule.fg_bot

lemma local_index_aux (P : Place) (m : ℤ) (d : ℕ) :
    Module.Finite k (Qt (V.Kge P (m + d)) (V.Kge P m)) ∧
      Module.finrank k (Qt (V.Kge P (m + d)) (V.Kge P m)) = d * V.degP P := by
  induction d with
  | zero =>
      rw [Nat.cast_zero, add_zero]
      exact ⟨finite_Qt_self (k := k) (V.Kge P m), by
        rw [finrank_Qt_self (k := k) (V.Kge P m)]; ring⟩
  | succ d ih =>
      obtain ⟨hfd, hrd⟩ := ih
      have hle1 : V.Kge P (m + d + 1) ≤ V.Kge P (m + d) := V.Kge_mono (by omega)
      have hle2 : V.Kge P (m + d) ≤ V.Kge P m := V.Kge_mono (by omega)
      have hf1 : Module.Finite k (Qt (V.Kge P (m + d + 1)) (V.Kge P (m + d))) :=
        finite_Qt_Kge_succ V hfin P (m + d)
      have hr1 : Module.finrank k (Qt (V.Kge P (m + d + 1)) (V.Kge P (m + d))) = V.degP P :=
        finrank_Qt_Kge_succ V hfin P (m + d)
      have heq : m + ((d : ℤ) + 1) = m + d + 1 := by ring
      constructor
      · rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by push_cast; ring, heq]
        exact finite_Qt_of_both hle1 hle2
      · rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by push_cast; ring, heq]
        rw [← finrank_Qt_add hle1 hle2, hr1, hrd]
        ring

lemma finite_local_index (P : Place) {m n : ℤ} (h : m ≤ n) :
    Module.Finite k (Qt (V.Kge P n) (V.Kge P m)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n = m + (d : ℤ) := ⟨(n - m).toNat, by omega⟩
  rw [hd]
  exact (local_index_aux V hfin P m d).1

lemma finrank_local_index (P : Place) {m n : ℤ} (h : m ≤ n) :
    Module.finrank k (Qt (V.Kge P n) (V.Kge P m)) = (n - m).toNat * V.degP P := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n = m + (d : ℤ) := ⟨(n - m).toNat, by omega⟩
  have hdn : (n - m).toNat = d := by omega
  rw [hdn, hd]
  exact (local_index_aux V hfin P m d).2

lemma one_le_degP (P : Place) : 1 ≤ V.degP P := by
  have := hfin P
  have h1 : (1 : K) ∈ V.Kge P 0 := by
    show ((0 : ℤ) : WithTop ℤ) ≤ V.ord P 1
    rw [V.ord_of_ne P one_ne_zero, V.v_one]
  have hne : Nontrivial (Qt (V.Kge P 1) (V.Kge P 0)) := by
    refine ⟨⟨Submodule.Quotient.mk ⟨1, h1⟩, 0, ?_⟩⟩
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    have h2 : (1 : K) ∈ V.Kge P 1 := hmem
    have h3 : ((1 : ℤ) : WithTop ℤ) ≤ V.ord P 1 := h2
    rw [V.ord_of_ne P one_ne_zero, V.v_one] at h3
    have h4 : (1 : ℤ) ≤ 0 := WithTop.coe_le_coe.mp h3
    omega
  exact Module.finrank_pos

end PlaceData

end Math2

/-
Divisors, their degrees, the Riemann-Roch spaces `L(D)`, and the axioms defining
the function field of a smooth projective curve.
-/
import RequestProject.RR.Divisor

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

/-- A divisor: a finitely supported integer combination of closed points. -/
abbrev Divisor (Place : Type*) := Place →₀ ℤ

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)

/-! ### Degree of a divisor -/

/-- The degree of a divisor. -/
noncomputable def deg (D : Divisor Place) : ℤ := D.sum fun P n => n * (V.degP P : ℤ)

@[simp] lemma deg_zero : V.deg (0 : Divisor Place) = 0 := by simp [deg]

lemma deg_add (D E : Divisor Place) : V.deg (D + E) = V.deg D + V.deg E := by
  simp only [deg]
  rw [Finsupp.sum_add_index' (by intro P; ring) (by intro P b₁ b₂; ring)]

lemma deg_neg (D : Divisor Place) : V.deg (-D) = - V.deg D := by
  have h := V.deg_add D (-D)
  rw [add_neg_cancel, deg_zero] at h
  omega

lemma deg_sub (D E : Divisor Place) : V.deg (D - E) = V.deg D - V.deg E := by
  rw [sub_eq_add_neg, deg_add, deg_neg, sub_eq_add_neg]

lemma deg_single (P : Place) (n : ℤ) : V.deg (Finsupp.single P n) = n * (V.degP P : ℤ) := by
  simp [deg, Finsupp.sum_single_index]

lemma deg_nonneg_of_nonneg {D : Divisor Place} (hD : 0 ≤ D) : 0 ≤ V.deg D := by
  refine Finset.sum_nonneg ?_
  intro P _
  have : 0 ≤ D P := by simpa using hD P
  positivity

lemma deg_mono {D E : Divisor Place} (h : D ≤ E) : V.deg D ≤ V.deg E := by
  have h0 : (0 : Divisor Place) ≤ E - D := by
    intro P; simpa using h P
  have := V.deg_nonneg_of_nonneg h0
  rw [deg_sub] at this
  omega

/-- If `D ≤ E` and the degrees agree, then `D = E` (using that places have positive degree). -/
lemma eq_of_le_of_deg_le (hfin : ∀ P : Place, Module.Finite k (Qt (V.Kge P 1) (V.Kge P 0)))
    {D E : Divisor Place} (h : D ≤ E) (hd : V.deg E ≤ V.deg D) : D = E := by
  classical
  by_contra hne
  obtain ⟨Q, hQ⟩ : ∃ Q, D Q ≠ E Q := by
    by_contra hc
    push_neg at hc
    exact hne (Finsupp.ext hc)
  have hQlt : D Q < E Q := lt_of_le_of_ne (h Q) hQ
  set F : Divisor Place := E - D with hF
  have hF0 : 0 ≤ F := by intro P; simpa [hF] using h P
  have hFQ : 0 < F Q := by simp [hF]; omega
  have hdegF : V.deg F ≤ 0 := by
    rw [deg_sub]; omega
  have hQmem : Q ∈ F.support := by
    simp only [Finsupp.mem_support_iff]
    omega
  have hpos : 0 < F Q * (V.degP Q : ℤ) := by
    have := V.one_le_degP hfin Q
    have h1 : (1 : ℤ) ≤ (V.degP Q : ℤ) := by exact_mod_cast this
    nlinarith
  have hsum : 0 < V.deg F := by
    rw [deg, Finsupp.sum, ← Finset.sum_erase_add _ _ hQmem]
    have hrest : 0 ≤ ∑ P ∈ F.support.erase Q, F P * (V.degP P : ℤ) := by
      refine Finset.sum_nonneg ?_
      intro P _
      have : 0 ≤ F P := by simpa using hF0 P
      positivity
    omega
  omega

/-! ### Riemann-Roch spaces -/

/-- The Riemann-Roch space `L(D) = {x : div x + D ≥ 0}`. -/
def Lspace (D : Divisor Place) : Submodule k K := ⨅ P : Place, V.Kge P (-(D P))

lemma mem_Lspace {D : Divisor Place} {x : K} :
    x ∈ V.Lspace D ↔ ∀ P : Place, ((-(D P) : ℤ) : WithTop ℤ) ≤ V.ord P x := by
  simp [Lspace, Submodule.mem_iInf]

lemma Lspace_mono {D E : Divisor Place} (h : D ≤ E) : V.Lspace D ≤ V.Lspace E := by
  intro x hx
  rw [mem_Lspace] at hx ⊢
  intro P
  refine le_trans ?_ (hx P)
  exact_mod_cast neg_le_neg (h P)

/-- The dimension of the Riemann-Roch space. -/
noncomputable def ell (D : Divisor Place) : ℕ := Module.finrank k (V.Lspace D)

/-! ### The principal divisor of a nonzero element -/

open scoped Classical in
/-- The divisor of zeros and poles of `x` (junk value `0` for `x = 0`). -/
noncomputable def divisorOf (x : K) : Divisor Place :=
  if hx : x = 0 then 0 else
    Finsupp.onFinset (V.v_finite_support hx).toFinset (fun P => V.v P x) (by
      intro P hP
      exact (Set.Finite.mem_toFinset _).2 hP)

lemma divisorOf_apply {x : K} (hx : x ≠ 0) (P : Place) : V.divisorOf x P = V.v P x := by
  simp [divisorOf, hx]

lemma mem_Lspace_iff_of_ne {D : Divisor Place} {x : K} (hx : x ≠ 0) :
    x ∈ V.Lspace D ↔ 0 ≤ V.divisorOf x + D := by
  rw [mem_Lspace]
  constructor
  · intro h P
    have := h P
    rw [V.ord_of_ne P hx] at this
    have h2 : -(D P) ≤ V.v P x := by exact_mod_cast this
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
    rw [V.divisorOf_apply hx]
    omega
  · intro h P
    have := h P
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [V.divisorOf_apply hx] at this
    rw [V.ord_of_ne P hx]
    exact_mod_cast (by omega : -(D P) ≤ V.v P x)

lemma divisorOf_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    V.divisorOf (x * y) = V.divisorOf x + V.divisorOf y := by
  ext P
  rw [V.divisorOf_apply (mul_ne_zero hx hy)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [V.divisorOf_apply hx, V.divisorOf_apply hy, V.v_mul P hx hy]

lemma map_Lspace (D : Divisor Place) {x : K} (hx : x ≠ 0) :
    (V.Lspace D).map ((mulEquiv (k := k) hx : K ≃ₗ[k] K) : K →ₗ[k] K)
      = V.Lspace (D - V.divisorOf x) := by
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    have hy' : y ∈ V.Lspace D := hy
    rw [mem_Lspace] at hy'
    rw [mem_Lspace]
    intro P
    show ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ) ≤ V.ord P (x * y)
    rw [V.ord_mul, V.ord_of_ne P hx]
    have hP := hy' P
    calc ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ)
        = ((V.v P x : ℤ) : WithTop ℤ) + ((-(D P) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          simp only [Finsupp.coe_sub, Pi.sub_apply]
          rw [V.divisorOf_apply hx]
          ring
      _ ≤ ((V.v P x : ℤ) : WithTop ℤ) + V.ord P y := add_le_add le_rfl hP
  · intro z hz
    rw [mem_Lspace] at hz
    refine ⟨x⁻¹ * z, ?_, ?_⟩
    · show x⁻¹ * z ∈ V.Lspace D
      rw [mem_Lspace]
      intro P
      have hP := hz P
      show ((-(D P) : ℤ) : WithTop ℤ) ≤ V.ord P (x⁻¹ * z)
      rw [V.ord_mul, V.ord_inv P hx]
      calc ((-(D P) : ℤ) : WithTop ℤ)
          = ((-(V.v P x) : ℤ) : WithTop ℤ) + ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]
            congr 1
            simp only [Finsupp.coe_sub, Pi.sub_apply]
            rw [V.divisorOf_apply hx]
            ring
        _ ≤ ((-(V.v P x) : ℤ) : WithTop ℤ) + V.ord P z := add_le_add le_rfl hP
    · show x * (x⁻¹ * z) = z
      field_simp

lemma ell_translate (D : Divisor Place) {x : K} (hx : x ≠ 0) :
    V.ell (D - V.divisorOf x) = V.ell D := by
  have e : V.Lspace D ≃ₗ[k] V.Lspace (D - V.divisorOf x) :=
    ((mulEquiv (k := k) hx).submoduleMap (V.Lspace D)).trans
      (LinearEquiv.ofEq _ _ (V.map_Lspace D hx))
  exact (e.finrank_eq).symm

end PlaceData

/-! ### Curve data -/

/-- The data of a smooth projective curve over `k`, presented through its function field `K`,
its set of closed points, and the orders of vanishing at those points.

The axioms are the standard elementary facts about the function field of a smooth
projective curve: the residue field at a closed point is a finite extension of `k`, a
principal divisor has degree `0`, the functions without poles are the constants, and
Riemann's inequality `ℓ(D) ≥ deg D + 1 - g₀` holds for some `g₀`. -/
structure CurveData (k K : Type*) [Field k] [Field K] [Algebra k K] (Place : Type*)
    extends PlaceData k K Place where
  /-- There is at least one closed point. -/
  place_nonempty : Nonempty Place
  /-- Residue fields are finite over `k`. -/
  residue_finite : ∀ P : Place,
    Module.Finite k (Qt (toPlaceData.Kge P 1) (toPlaceData.Kge P 0))
  /-- Principal divisors have degree zero. -/
  deg_principal : ∀ {x : K}, x ≠ 0 → toPlaceData.deg (toPlaceData.divisorOf x) = 0
  /-- A function without poles is constant. -/
  constants : ∀ x : K, (∀ P : Place, (0 : WithTop ℤ) ≤ toPlaceData.ord P x) →
    ∃ c : k, x = algebraMap k K c
  /-- Riemann's inequality. -/
  riemann : ∃ g₀ : ℕ, ∀ D : Divisor Place,
    toPlaceData.deg D + 1 - (g₀ : ℤ) ≤ (toPlaceData.ell D : ℤ)

end Math2

