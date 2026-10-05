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

import Mathlib
import RequestProject.PolySpace

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Unbounded fan-in Boolean circuits and their low-degree approximation

We define constant-depth, unbounded fan-in Boolean circuits over the basis
`{¬, ∨, ∧}` and prove Razborov's approximation lemma: a circuit of size `s`
and depth `d` is computed by a function of `F₃`-degree at most `(2ℓ)^d`
on all but a `s·2^{-ℓ}` fraction of the inputs.
-/

namespace CS

open Finset

/-- Unbounded fan-in Boolean circuits on `n` inputs. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | cst : Bool → Circ n
  | neg : Circ n → Circ n
  | orG : (k : ℕ) → (Fin k → Circ n) → Circ n
  | andG : (k : ℕ) → (Fin k → Circ n) → Circ n

/-- The Boolean function computed by a circuit. -/
def eval {n : ℕ} : Circ n → Inp n → Bool
  | .var i, x => x i
  | .cst b, _ => b
  | .neg c, x => !(eval c x)
  | .orG _ f, x => decide (∃ i, eval (f i) x = true)
  | .andG _ f, x => decide (∀ i, eval (f i) x = true)

/-- The depth of a circuit (number of gates on a longest input-output path). -/
def depth {n : ℕ} : Circ n → ℕ
  | .var _ => 0
  | .cst _ => 0
  | .neg c => depth c + 1
  | .orG _ f => (Finset.univ.sup fun i => depth (f i)) + 1
  | .andG _ f => (Finset.univ.sup fun i => depth (f i)) + 1

/-- The size of a circuit (total number of nodes). -/
def size {n : ℕ} : Circ n → ℕ
  | .var _ => 1
  | .cst _ => 1
  | .neg c => size c + 1
  | .orG _ f => (∑ i, size (f i)) + 1
  | .andG _ f => (∑ i, size (f i)) + 1

@[simp] lemma depth_orG {n k : ℕ} (f : Fin k → Circ n) :
    depth (Circ.orG k f) = (Finset.univ.sup fun i => depth (f i)) + 1 := rfl
@[simp] lemma depth_andG {n k : ℕ} (f : Fin k → Circ n) :
    depth (Circ.andG k f) = (Finset.univ.sup fun i => depth (f i)) + 1 := rfl
@[simp] lemma size_orG {n k : ℕ} (f : Fin k → Circ n) :
    size (Circ.orG k f) = (∑ i, size (f i)) + 1 := rfl
@[simp] lemma size_andG {n k : ℕ} (f : Fin k → Circ n) :
    size (Circ.andG k f) = (∑ i, size (f i)) + 1 := rfl

/-! ### A halving lemma for random `F₃` subset sums -/

/-- If `v` is a `0/1` vector with `v i₀ = 1`, then at most half of the `2^k` subsets
have vanishing subset sum. -/
lemma card_zero_subset_sums {k : ℕ} (v : Fin k → F3) (i₀ : Fin k) (h₀ : v i₀ = 1) :
    2 * ((Finset.univ.filter
        (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)).card) ≤ 2 ^ k := by
  classical
  set Z := (Finset.univ.filter
      (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)) with hZ
  set φ : (Fin k → Bool) → (Fin k → Bool) := fun a => Function.update a i₀ (!a i₀) with hφ
  have hsum : ∀ a : Fin k → Bool, ∑ i, (if a i then v i else 0)
      = (if a i₀ then v i₀ else 0) + ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0) := by
    intro a
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hφsum : ∀ a : Fin k → Bool, ∑ i, (if φ a i then v i else 0)
      = (if !a i₀ then v i₀ else 0) + ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0) := by
    intro a
    rw [hsum (φ a)]
    congr 1
    · simp [hφ]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ≠ i₀ := (Finset.mem_erase.1 hi).1
      simp [hφ, Function.update_of_ne this]
  have hmaps : ∀ a ∈ Z, φ a ∈ Finset.univ \ Z := by
    intro a ha
    have ha' : ∑ i, (if a i then v i else 0) = 0 := by
      simpa [hZ] using ha
    have hT : ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0)
        = -(if a i₀ then v i₀ else 0) := by
      have := hsum a
      rw [ha'] at this
      linear_combination -this
    have : ∑ i, (if φ a i then v i else 0) ≠ 0 := by
      rw [hφsum a, hT, h₀]
      cases a i₀ <;> decide
    simp [hZ, this]
  have hinj : Set.InjOn φ ↑Z := by
    intro a _ b _ hab
    have hinv : ∀ c : Fin k → Bool, φ (φ c) = c := by
      intro c
      funext i
      by_cases hi : i = i₀
      · subst hi; simp [hφ]
      · simp [hφ, Function.update_of_ne hi]
    have := hinv a
    have hb := hinv b
    rw [← this, ← hb, hab]
  have hcard : Z.card ≤ (Finset.univ \ Z).card :=
    Finset.card_le_card_of_injOn φ (fun a ha => by
      have h := hmaps a (by simpa using ha)
      simpa using h) hinj
  have huniv : (Finset.univ : Finset (Fin k → Bool)).card = 2 ^ k := by simp
  have hsub : (Finset.univ \ Z).card = 2 ^ k - Z.card := by
    rw [Finset.card_univ_diff]
    simp
  have hZle : Z.card ≤ 2 ^ k := by rw [← huniv]; exact Finset.card_le_univ Z
  omega

/-! ### The approximator for a single gate -/

/-- Razborov's approximator for an unbounded fan-in OR of the functions `g i`,
using the `ℓ` random subsets given by `r`. -/
def orApprox {n k ℓ : ℕ} (g : Fin k → Fn n) (r : Fin ℓ → Fin k → Bool) : Fn n :=
  1 - ∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i else 0)) ^ 2)

lemma orApprox_apply {n k ℓ : ℕ} (g : Fin k → Fn n) (r : Fin ℓ → Fin k → Bool) (x : Inp n) :
    orApprox g r x = 1 - ∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i x else 0)) ^ 2) := by
  simp only [orApprox, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply,
    Finset.sum_apply, Pi.zero_apply]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : r j i <;> simp [h]

lemma orApprox_mem {n k ℓ D : ℕ} (g : Fin k → Fn n) (hg : ∀ i, g i ∈ V n D)
    (r : Fin ℓ → Fin k → Bool) : orApprox g r ∈ V n (2 * ℓ * D) := by
  have hfac : ∀ j : Fin ℓ,
      (1 - (∑ i : Fin k, (if r j i then g i else 0)) ^ 2) ∈ V n (2 * D) := by
    intro j
    have hs : (∑ i : Fin k, (if r j i then g i else 0)) ∈ V n D := by
      refine Submodule.sum_mem _ (fun i _ => ?_)
      by_cases h : r j i
      · simpa [h] using hg i
      · simp [h]
    have : (∑ i : Fin k, (if r j i then g i else 0)) ^ 2 ∈ V n (D + D) := by
      rw [pow_two]; exact V_mul hs hs
    refine Submodule.sub_mem _ one_mem_V (V_mono ?_ this)
    omega
  have hprod : (∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i else 0)) ^ 2))
      ∈ V n ((Finset.univ : Finset (Fin ℓ)).card * (2 * D)) := by
    refine prod_mem_pow (V n) (fun _ => one_mem_V) (fun hf hg => V_mul hf hg) _ _ _
      (fun j _ => hfac j)
  refine Submodule.sub_mem _ one_mem_V (V_mono ?_ hprod)
  simp only [Finset.card_univ, Fintype.card_fin]
  exact le_of_eq (by ring)

/-! ### The gate lemma -/

lemma or_step {n : ℕ} (k ℓ D : ℕ) (g : Fin k → Fn n) (hg : ∀ i, g i ∈ V n D)
    (b : Fin k → Inp n → Bool) (U : Finset (Inp n))
    (hU : ∀ x ∈ U, ∀ i, g i x = bf (b i x)) :
    ∃ G ∈ V n (2 * ℓ * D),
      (U.filter (fun x => G x ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ ≤ U.card := by
  classical
  -- the set of choices
  set R : Finset (Fin ℓ → Fin k → Bool) := Finset.univ with hR
  have hRcard : R.card = (2 ^ k) ^ ℓ := by
    rw [hR, Finset.card_univ, Fintype.card_fun, Fintype.card_fun]
    simp
  -- for each fixed input, few choices are bad
  have key : ∀ x ∈ U, ((R.filter
      (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ ≤ R.card := by
    intro x hx
    by_cases hex : ∃ i, b i x = true
    · obtain ⟨i₀, hi₀⟩ := hex
      set v : Fin k → F3 := fun i => g i x with hv
      have hv₀ : v i₀ = 1 := by rw [hv]; simp [hU x hx i₀, hi₀]
      set Z := (Finset.univ.filter
          (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)) with hZ
      have hZhalf : 2 * Z.card ≤ 2 ^ k := card_zero_subset_sums v i₀ hv₀
      -- bad choices all lie in the product set `Z^ℓ`
      have hsub : (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true))))
          ⊆ Fintype.piFinset (fun _ : Fin ℓ => Z) := by
        intro r hr
        simp only [Finset.mem_filter] at hr
        refine Fintype.mem_piFinset.2 (fun j => ?_)
        by_contra hj
        have hjne : (∑ i, (if r j i then v i else 0)) ≠ 0 := by
          simpa [hZ] using hj
        have : orApprox g r x = 1 := by
          rw [orApprox_apply]
          have : (∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i x else 0)) ^ 2)) = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            have hsq : (∑ i : Fin k, (if r j i then v i else 0)) ^ 2 = 1 := by
              revert hjne
              generalize (∑ i : Fin k, (if r j i then v i else 0)) = c
              decide +revert
            rw [show (∑ i : Fin k, (if r j i then g i x else 0))
                = (∑ i : Fin k, (if r j i then v i else 0)) from rfl, hsq]
            ring
          rw [this]; ring
        rw [this] at hr
        have : bf (decide (∃ i, b i x = true)) = 1 := by
          simp only [bf, decide_eq_true_eq, if_pos (⟨i₀, hi₀⟩ : ∃ i, b i x = true)]
        exact hr.2 (by rw [this])
      have hcard := Finset.card_le_card hsub
      rw [Fintype.card_piFinset] at hcard
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
      calc (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ
          ≤ Z.card ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul_right _ hcard
        _ = (Z.card * 2) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left (by omega) ℓ
        _ = R.card := hRcard.symm
    · -- the OR is false: the approximator is exactly correct
      have hall : ∀ i, b i x = false := by
        intro i; cases h : b i x
        · rfl
        · exact absurd ⟨i, h⟩ hex
      have hzero : ∀ r : Fin ℓ → Fin k → Bool, orApprox g r x = 0 := by
        intro r
        rw [orApprox_apply]
        have : ∀ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i x else 0)) ^ 2) = 1 := by
          intro j
          have : (∑ i : Fin k, (if r j i then g i x else 0)) = 0 := by
            refine Finset.sum_eq_zero (fun i _ => ?_)
            by_cases h : r j i
            · simp [h, hU x hx i, hall i]
            · simp [h]
          rw [this]; ring
        rw [Finset.prod_congr rfl (fun j _ => this j)]
        simp
      have : (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 (fun r _ => ?_)
        rw [hzero r]
        simp [bf, hex]
      rw [this]
      simp
  -- double counting
  have hdc : ∑ r ∈ R, ((U.filter (fun x => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card
        * 2 ^ ℓ) ≤ ∑ _r ∈ R, U.card := by
    have hswap : ∑ r ∈ R, (U.filter (fun x => orApprox g r x
          ≠ bf (decide (∃ i, b i x = true)))).card
        = ∑ x ∈ U, (R.filter (fun r => orApprox g r x
          ≠ bf (decide (∃ i, b i x = true)))).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    calc ∑ r ∈ R, ((U.filter (fun x => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ)
        = (∑ r ∈ R, (U.filter (fun x => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ := by
          rw [Finset.sum_mul]
      _ = (∑ x ∈ U, (R.filter (fun r => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ := by rw [hswap]
      _ = ∑ x ∈ U, ((R.filter (fun r => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ) := by rw [Finset.sum_mul]
      _ ≤ ∑ _x ∈ U, R.card := Finset.sum_le_sum key
      _ = U.card * R.card := by rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ _r ∈ R, U.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨r, _, hr⟩ := Finset.exists_le_of_sum_le ⟨(fun _ _ => false), Finset.mem_univ _⟩ hdc
  exact ⟨orApprox g r, orApprox_mem g hg r, hr⟩

end CS

import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The space of `F₃`-valued functions on the Boolean cube

We set up the "low degree" filtration of the space of functions
`(Fin n → Bool) → ZMod 3`, both in the `x`-coordinates (`x i ∈ {0,1}`)
and in the `y`-coordinates (`y i = 1 + x i ∈ {1,-1}`), and show that the two
filtrations coincide.
-/

namespace CS

open Finset

/-- The field with three elements. -/
abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Booleans as elements of `F₃`. -/
def bf : Bool → F3 := fun b => if b then 1 else 0

@[simp] lemma bf_true : bf true = 1 := rfl
@[simp] lemma bf_false : bf false = 0 := rfl

lemma bf_mul_self (b : Bool) : bf b * bf b = bf b := by cases b <;> decide

lemma bf_eq_zero_iff (b : Bool) : bf b = 0 ↔ b = false := by cases b <;> decide

lemma bf_ne (b : Bool) : bf (!b) = 1 - bf b := by cases b <;> decide

/-- Inputs: Boolean strings of length `n`. -/
abbrev Inp (n : ℕ) := Fin n → Bool

/-- `F₃`-valued functions on the Boolean cube. -/
abbrev Fn (n : ℕ) := Inp n → F3

/-! ### Two auxiliary product identities -/

lemma prod_split {ι M : Type*} [CommMonoid M] [DecidableEq ι] (v : ι → M) (S T : Finset ι) :
    ((∏ i ∈ S, v i) * ∏ i ∈ T, v i)
      = (∏ i ∈ S \ T, v i) * (∏ i ∈ T \ S, v i) * ((∏ i ∈ S ∩ T, v i) * ∏ i ∈ S ∩ T, v i) := by
  have hS : (∏ i ∈ S \ T, v i) * (∏ i ∈ S ∩ T, v i) = ∏ i ∈ S, v i := by
    rw [← Finset.prod_union (by simp [Finset.disjoint_left]; tauto)]
    congr 1; ext a; simp; tauto
  have hT : (∏ i ∈ T \ S, v i) * (∏ i ∈ S ∩ T, v i) = ∏ i ∈ T, v i := by
    rw [← Finset.prod_union (by simp [Finset.disjoint_left]; tauto)]
    congr 1; ext a; simp; tauto
  rw [← hS, ← hT]; simp [mul_comm, mul_assoc, mul_left_comm]

lemma prod_union_eq {ι M : Type*} [CommMonoid M] [DecidableEq ι] (v : ι → M) (S T : Finset ι) :
    (∏ i ∈ S ∪ T, v i) = (∏ i ∈ S \ T, v i) * (∏ i ∈ T \ S, v i) * (∏ i ∈ S ∩ T, v i) := by
  have h1 : (∏ i ∈ (S \ T) ∪ (T \ S), v i) * (∏ i ∈ S ∩ T, v i) = ∏ i ∈ S ∪ T, v i := by
    rw [← Finset.prod_union (by simp [Finset.disjoint_left]; tauto)]
    congr 1; ext a; simp; tauto
  rw [← h1, Finset.prod_union (by simp [Finset.disjoint_left]; tauto)]

lemma prod_symmDiff_eq {ι M : Type*} [CommMonoid M] [DecidableEq ι] (v : ι → M) (S T : Finset ι) :
    (∏ i ∈ symmDiff S T, v i) = (∏ i ∈ S \ T, v i) * (∏ i ∈ T \ S, v i) := by
  rw [← Finset.prod_union (by simp [Finset.disjoint_left]; tauto)]
  congr 1

lemma card_symmDiff_le {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (symmDiff S T).card ≤ S.card + T.card := by
  have h : symmDiff S T ⊆ S ∪ T := by
    rw [← Finset.sup_eq_union]; exact (symmDiff_le_sup : symmDiff S T ≤ S ⊔ T)
  exact le_trans (Finset.card_le_card h) (Finset.card_union_le _ _)

/-! ### Monomials and the degree filtration -/

/-- The monomial `∏_{i ∈ S} x i`. -/
def mon {n : ℕ} (S : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ S, bf (x i)

/-- The `±1`-monomial `∏_{i ∈ S} (1 + x i)`. -/
def monY {n : ℕ} (S : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ S, (1 + bf (x i))

/-- Functions of degree at most `D` in the `x` variables. -/
def V (n D : ℕ) : Submodule F3 (Fn n) :=
  Submodule.span F3 {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = mon S}

/-- Functions of degree at most `D` in the `y` variables. -/
def W (n D : ℕ) : Submodule F3 (Fn n) :=
  Submodule.span F3 {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = monY S}

lemma mon_mem_V {n D : ℕ} {S : Finset (Fin n)} (h : S.card ≤ D) : mon S ∈ V n D :=
  Submodule.subset_span ⟨S, h, rfl⟩

lemma monY_mem_W {n D : ℕ} {S : Finset (Fin n)} (h : S.card ≤ D) : monY S ∈ W n D :=
  Submodule.subset_span ⟨S, h, rfl⟩

lemma V_mono {n : ℕ} : Monotone (V n) := by
  intro a b hab
  exact Submodule.span_mono (by rintro f ⟨S, hS, rfl⟩; exact ⟨S, hS.trans hab, rfl⟩)

lemma W_mono {n : ℕ} : Monotone (W n) := by
  intro a b hab
  exact Submodule.span_mono (by rintro f ⟨S, hS, rfl⟩; exact ⟨S, hS.trans hab, rfl⟩)

@[simp] lemma mon_empty {n : ℕ} : mon (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mon]

@[simp] lemma monY_empty {n : ℕ} : monY (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [monY]

lemma one_mem_V {n D : ℕ} : (1 : Fn n) ∈ V n D := by
  simpa using mon_mem_V (S := (∅ : Finset (Fin n))) (D := D) (by simp)

lemma one_mem_W {n D : ℕ} : (1 : Fn n) ∈ W n D := by
  simpa using monY_mem_W (S := (∅ : Finset (Fin n))) (D := D) (by simp)

lemma mon_mul {n : ℕ} (S T : Finset (Fin n)) : mon S * mon T = mon (S ∪ T) := by
  funext x
  show (∏ i ∈ S, bf (x i)) * (∏ i ∈ T, bf (x i)) = ∏ i ∈ S ∪ T, bf (x i)
  rw [prod_split, prod_union_eq, ← Finset.prod_mul_distrib]
  simp [bf_mul_self]

lemma monY_mul {n : ℕ} (S T : Finset (Fin n)) : monY S * monY T = monY (symmDiff S T) := by
  funext x
  show (∏ i ∈ S, (1 + bf (x i))) * (∏ i ∈ T, (1 + bf (x i)))
      = ∏ i ∈ symmDiff S T, (1 + bf (x i))
  rw [prod_split, prod_symmDiff_eq, ← Finset.prod_mul_distrib]
  have : ∀ i, (1 + bf (x i)) * (1 + bf (x i)) = 1 := by
    intro i; cases x i <;> decide
  simp [this]

lemma V_mul {n D₁ D₂ : ℕ} {f g : Fn n} (hf : f ∈ V n D₁) (hg : g ∈ V n D₂) :
    f * g ∈ V n (D₁ + D₂) := by
  have key : V n D₁ * V n D₂ ≤ V n (D₁ + D₂) := by
    rw [V, V, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro h ⟨a, ⟨S, hS, rfl⟩, b, ⟨T, hT, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨S ∪ T, ?_, mon_mul S T⟩
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add hS hT)
  exact key (Submodule.mul_mem_mul hf hg)

lemma W_mul {n D₁ D₂ : ℕ} {f g : Fn n} (hf : f ∈ W n D₁) (hg : g ∈ W n D₂) :
    f * g ∈ W n (D₁ + D₂) := by
  have key : W n D₁ * W n D₂ ≤ W n (D₁ + D₂) := by
    rw [W, W, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro h ⟨a, ⟨S, hS, rfl⟩, b, ⟨T, hT, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨symmDiff S T, ?_, monY_mul S T⟩
    exact le_trans (card_symmDiff_le S T) (Nat.add_le_add hS hT)
  exact key (Submodule.mul_mem_mul hf hg)

/-- A product of `S.card` functions of degree `≤ 1` has degree `≤ S.card`. -/
lemma prod_mem_graded {n : ℕ} (U : ℕ → Submodule F3 (Fn n))
    (hone : ∀ D, (1 : Fn n) ∈ U D)
    (hmul : ∀ {D₁ D₂ : ℕ} {f g : Fn n}, f ∈ U D₁ → g ∈ U D₂ → f * g ∈ U (D₁ + D₂))
    (S : Finset (Fin n)) (h : Fin n → Fn n) (hh : ∀ i ∈ S, h i ∈ U 1) :
    (∏ i ∈ S, h i) ∈ U S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hone 0
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : h a ∈ U 1 := hh a (by simp)
      have h2 : (∏ i ∈ S, h i) ∈ U S.card := ih (fun i hi => hh i (by simp [hi]))
      have h3 := hmul h1 h2
      rwa [show 1 + S.card = S.card + 1 by ring] at h3

/-- A product of `s.card` functions of degree `≤ D` has degree `≤ s.card * D`. -/
lemma prod_mem_pow {n : ℕ} {ι : Type*} (U : ℕ → Submodule F3 (Fn n))
    (hone : ∀ D, (1 : Fn n) ∈ U D)
    (hmul : ∀ {D₁ D₂ : ℕ} {f g : Fn n}, f ∈ U D₁ → g ∈ U D₂ → f * g ∈ U (D₁ + D₂))
    (s : Finset ι) (h : ι → Fn n) (D : ℕ) (hh : ∀ i ∈ s, h i ∈ U D) :
    (∏ i ∈ s, h i) ∈ U (s.card * D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hone 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : h a ∈ U D := hh a (by simp)
      have h2 : (∏ i ∈ s, h i) ∈ U (s.card * D) := ih (fun i hi => hh i (by simp [hi]))
      have h3 := hmul h1 h2
      rwa [show D + s.card * D = (s.card + 1) * D by ring] at h3

lemma prod_mem_V {n : ℕ} (S : Finset (Fin n)) (h : Fin n → Fn n) (hh : ∀ i ∈ S, h i ∈ V n 1) :
    (∏ i ∈ S, h i) ∈ V n S.card :=
  prod_mem_graded (V n) (fun _ => one_mem_V) (fun hf hg => V_mul hf hg) S h hh

lemma prod_mem_W {n : ℕ} (S : Finset (Fin n)) (h : Fin n → Fn n) (hh : ∀ i ∈ S, h i ∈ W n 1) :
    (∏ i ∈ S, h i) ∈ W n S.card :=
  prod_mem_graded (W n) (fun _ => one_mem_W) (fun hf hg => W_mul hf hg) S h hh

/-! ### The two filtrations agree -/

/-- The coordinate function `x ↦ x i`. -/
def xvar {n : ℕ} (i : Fin n) : Fn n := fun x => bf (x i)

lemma xvar_eq_mon {n : ℕ} (i : Fin n) : xvar i = mon {i} := by
  funext x; simp [xvar, mon]

lemma xvar_mem_V {n : ℕ} (i : Fin n) : xvar i ∈ V n 1 := by
  rw [xvar_eq_mon]; exact mon_mem_V (by simp)

lemma xvar_mem_W {n : ℕ} (i : Fin n) : xvar i ∈ W n 1 := by
  have h : xvar i = monY {i} - 1 := by
    funext x; simp [xvar, monY]
  rw [h]
  exact Submodule.sub_mem _ (monY_mem_W (by simp)) one_mem_W

lemma V_le_W {n D : ℕ} : V n D ≤ W n D := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨S, hS, rfl⟩
  have h1 : mon S = ∏ i ∈ S, xvar i := by
    funext x; simp [mon, xvar]
  rw [h1]
  exact W_mono hS (prod_mem_W S _ (fun i _ => xvar_mem_W i))

lemma W_le_V {n D : ℕ} : W n D ≤ V n D := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨S, hS, rfl⟩
  have h1 : monY S = ∏ i ∈ S, (1 + xvar i) := by
    funext x; simp [monY, xvar]
  rw [h1]
  refine V_mono hS (prod_mem_V S _ (fun i _ => ?_))
  exact Submodule.add_mem _ one_mem_V (xvar_mem_V i)

lemma V_eq_W {n D : ℕ} : V n D = W n D := le_antisymm V_le_W W_le_V

/-! ### The full space -/

/-- The indicator function of a point of the cube. -/
def ind {n : ℕ} (x₀ : Inp n) : Fn n := fun x => ∏ i, (if x₀ i then bf (x i) else 1 - bf (x i))

lemma ind_apply {n : ℕ} (x₀ x : Inp n) : ind x₀ x = if x = x₀ then 1 else 0 := by
  classical
  by_cases h : x = x₀
  · subst h
    simp only [ind, if_pos rfl]
    refine Finset.prod_eq_one (fun i _ => ?_)
    cases x i <;> decide
  · simp only [ind, if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x₀ i := by
      by_contra hc
      exact h (funext (by simpa using not_exists.1 hc))
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hb : x₀ i <;> cases hb' : x i <;> simp [hb, hb'] at hi ⊢

lemma ind_mem_V {n : ℕ} (x₀ : Inp n) : ind x₀ ∈ V n n := by
  have h : ind x₀ = ∏ i : Fin n, (fun x : Inp n => if x₀ i then bf (x i) else 1 - bf (x i)) := by
    funext x; simp [ind]
  rw [h]
  have := prod_mem_V (Finset.univ : Finset (Fin n))
    (fun i => (fun x : Inp n => if x₀ i then bf (x i) else 1 - bf (x i)))
    (fun i _ => by
      by_cases hb : x₀ i
      · simpa [hb] using xvar_mem_V i
      · simp only [hb, if_false]
        exact Submodule.sub_mem _ one_mem_V (xvar_mem_V i))
  simpa using this

lemma V_top {n : ℕ} : V n n = ⊤ := by
  classical
  refine eq_top_iff.2 (fun f _ => ?_)
  have h : f = ∑ x₀ : Inp n, f x₀ • ind x₀ := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp [ind_apply]
    · intro b _ hb
      simp [ind_apply, Ne.symm hb]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [h]
  exact Submodule.sum_mem _ (fun x₀ _ => Submodule.smul_mem _ _ (ind_mem_V x₀))

lemma W_top {n : ℕ} : W n n = ⊤ := by rw [← V_eq_W]; exact V_top

end CS

