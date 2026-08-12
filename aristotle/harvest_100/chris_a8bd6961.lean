/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Cauchy's theorem: if a prime `p` divides the order of a finite group `G`, then `G` contains an
element of order `p`.  The proof given here is McKay's counting argument, carried out from
first principles: the cyclic group of order `p` acts by rotation on the set of `p`-tuples of
elements of `G` whose ordered product is `1`, that set has cardinality `|G| ^ (p - 1)`, and the
fixed points of the action are exactly the constant tuples `(g, …, g)` with `g ^ p = 1`.
-/

namespace Math

open MulAction

variable {G : Type*} [Group G]

/-! ### Tuples with product one -/

/-- The set of `n`-tuples of elements of `G` whose (ordered) product is `1`. -/
def ProdOne (G : Type*) [Group G] (n : ℕ) : Type _ :=
  {v : Fin n → G // (List.ofFn v).prod = 1}

instance {G : Type*} [Group G] [Finite G] (n : ℕ) : Finite (ProdOne G n) :=
  Subtype.finite

lemma prod_ofFn_split {n : ℕ} (f : Fin (n + 1) → G) :
    (List.ofFn f).prod = (List.ofFn (Fin.init f)).prod * f (Fin.last n) := by
  rw [List.ofFn_succ', List.prod_concat]; rfl

/-- Dropping the last coordinate identifies tuples with product one with arbitrary tuples of
length one less. -/
def prodOneEquiv (G : Type*) [Group G] (n : ℕ) : ProdOne G (n + 1) ≃ (Fin n → G) where
  toFun v := Fin.init v.1
  invFun w := ⟨Fin.snoc w ((List.ofFn w).prod⁻¹), by
    rw [prod_ofFn_split, Fin.snoc_last, Fin.init_snoc, mul_inv_cancel]⟩
  left_inv v := by
    apply Subtype.ext
    have h : (List.ofFn (Fin.init v.1)).prod⁻¹ = v.1 (Fin.last n) :=
      inv_eq_of_mul_eq_one_right (by rw [← prod_ofFn_split, v.2])
    simp only [h, Fin.snoc_init_self]
  right_inv w := by simp [Fin.init_snoc]

lemma card_prodOne (G : Type*) [Group G] [Finite G] (n : ℕ) :
    Nat.card (ProdOne G (n + 1)) = Nat.card G ^ n := by
  rw [Nat.card_congr (prodOneEquiv G n), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]

/-! ### The rotation action -/

/-- Cyclic shift of a tuple by `m` places. -/
def shiftFun {n : ℕ} (m : ℕ) (v : Fin (n + 1) → G) : Fin (n + 1) → G :=
  fun i => v ⟨(i.val + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

omit [Group G] in
lemma ofFn_shiftFun {n : ℕ} (v : Fin (n + 1) → G) (m : ℕ) :
    List.ofFn (shiftFun m v) = (List.ofFn v).rotate m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, List.getElem_rotate, List.length_ofFn, shiftFun]

omit [Group G] in
lemma shiftFun_shiftFun {n : ℕ} (v : Fin (n + 1) → G) (a b : ℕ) :
    shiftFun a (shiftFun b v) = shiftFun ((a + b) % (n + 1)) v := by
  funext i
  simp only [shiftFun]
  congr 1
  ext
  simp [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

omit [Group G] in
lemma shiftFun_zero {n : ℕ} (v : Fin (n + 1) → G) : shiftFun 0 v = v := by
  funext i
  simp [shiftFun, Nat.mod_eq_of_lt i.isLt]

/-- The rotation action of the cyclic group of order `n + 1` on tuples with product one. -/
instance rotAction (G : Type*) [Group G] (n : ℕ) :
    MulAction (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1)) where
  smul k v := ⟨shiftFun (k.toAdd.val) v.1, by
    rw [ofFn_shiftFun]
    exact List.prod_rotate_eq_one_of_prod_eq_one v.2 _⟩
  one_smul v := by
    apply Subtype.ext
    show shiftFun _ v.1 = v.1
    simpa using shiftFun_zero v.1
  mul_smul a b v := by
    apply Subtype.ext
    show shiftFun _ v.1 = shiftFun _ (shiftFun _ v.1)
    rw [shiftFun_shiftFun]
    congr 1

lemma smul_prodOne_coe (n : ℕ) (k : Multiplicative (ZMod (n + 1))) (v : ProdOne G (n + 1)) :
    (k • v).1 = shiftFun (k.toAdd.val) v.1 := rfl

/-! ### Fixed points -/

/-- The all-ones tuple has product one. -/
def trivialTuple (G : Type*) [Group G] (n : ℕ) : ProdOne G n := ⟨fun _ => 1, by simp⟩

lemma trivialTuple_mem_fixedPoints (n : ℕ) :
    trivialTuple G (n + 1) ∈ fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1)) := by
  intro k
  apply Subtype.ext
  rw [smul_prodOne_coe]
  rfl

/-- A fixed tuple is constant, and its common value has `p`-th power one. -/
lemma fixedPoint_const {n : ℕ} (v : ProdOne G (n + 1))
    (hv : v ∈ fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1))) (i : Fin (n + 1)) :
    v.1 i = v.1 0 := by
  have hk := hv (Multiplicative.ofAdd ((i.val : ℕ) : ZMod (n + 1)))
  have hk' := congrArg (fun w => (Subtype.val w) (0 : Fin (n + 1))) hk
  simp only [smul_prodOne_coe, shiftFun] at hk'
  have hval : ((i.val : ℕ) : ZMod (n + 1)).val = i.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt i.isLt
  rw [show (Multiplicative.ofAdd ((i.val : ℕ) : ZMod (n + 1))).toAdd
      = ((i.val : ℕ) : ZMod (n + 1)) from rfl, hval] at hk'
  simpa [Nat.mod_eq_of_lt i.isLt] using hk'

lemma fixedPoint_pow {n : ℕ} (v : ProdOne G (n + 1))
    (hv : v ∈ fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1))) :
    (v.1 0) ^ (n + 1) = 1 := by
  have h : List.ofFn v.1 = List.replicate (n + 1) (v.1 0) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      rw [List.getElem_ofFn, List.getElem_replicate]
      exact fixedPoint_const v hv _
  have := v.2
  rw [h, List.prod_replicate] at this
  exact this

/-! ### Cauchy's theorem -/

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`, then `G` has an
element of order `p`. -/
theorem cauchy_group {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hIsP : IsPGroup (n + 1) (Multiplicative (ZMod (n + 1))) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_eq_fintype_card])
  have hmod := hIsP.card_modEq_card_fixedPoints (ProdOne G (n + 1))
  rw [card_prodOne] at hmod
  set F := fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1))
  have hdvdpow : (n + 1) ∣ Nat.card G ^ n := dvd_pow hdvd hn
  have hdvdF : (n + 1) ∣ Nat.card F := by
    rw [← Nat.modEq_zero_iff_dvd]
    calc Nat.card F ≡ Nat.card G ^ n [MOD n + 1] := hmod.symm
      _ ≡ 0 [MOD n + 1] := (Nat.modEq_zero_iff_dvd).2 hdvdpow
  haveI : Nonempty F := ⟨⟨trivialTuple G (n + 1), trivialTuple_mem_fixedPoints n⟩⟩
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hlt : 1 < Nat.card F := by
    have := Nat.le_of_dvd hpos hdvdF
    omega
  haveI : Nontrivial F := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨v, hv⟩ := exists_ne (⟨trivialTuple G (n + 1), trivialTuple_mem_fixedPoints n⟩ : F)
  refine ⟨v.1.1 0, orderOf_eq_prime (fixedPoint_pow v.1 v.2) ?_⟩
  intro hone
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext i
  rw [fixedPoint_const v.1 v.2 i, hone]
  rfl

/-- **Cauchy's theorem**, stated with `Fintype.card`. -/
theorem cauchy_group_fintype {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  cauchy_group hp (by rwa [Nat.card_eq_fintype_card])

end Math

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

