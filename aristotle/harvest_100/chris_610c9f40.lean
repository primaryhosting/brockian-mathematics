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

/-!
## Characters and low-degree functions over `𝔽₃`

Boolean inputs are encoded multiplicatively: `true ↦ -1`, `false ↦ 1` (`CS.sgn`),
and also additively `true ↦ 1`, `false ↦ 0` (`CS.bit`).

For `S : Finset (Fin n)` the *character* `chi S` is the multilinear monomial
`x ↦ ∏ i ∈ S, sgn (x i)`; `V n D` is the space of functions `(Fin n → Bool) → 𝔽₃`
spanned by characters of degree at most `D`.
-/

namespace CS

/-- The field with three elements. -/
abbrev F : Type := ZMod 3

/-- Boolean inputs on `n` variables. -/
abbrev Inp (n : ℕ) : Type := Fin n → Bool

/-- Multiplicative (`±1`) encoding of a bit. -/
def sgn (b : Bool) : F := if b then -1 else 1

/-- Additive (`0/1`) encoding of a bit. -/
def bit (b : Bool) : F := if b then 1 else 0

@[simp] lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> decide

/-- The multilinear monomial (character) attached to a set of coordinates. -/
def chi {n : ℕ} (S : Finset (Fin n)) : Inp n → F := fun x => ∏ i ∈ S, sgn (x i)

lemma chi_empty {n : ℕ} : chi (∅ : Finset (Fin n)) = 1 := by funext x; simp [chi]

lemma chi_apply_prod_univ {n : ℕ} (S : Finset (Fin n)) (x : Inp n) :
    chi S x = ∏ i : Fin n, (if i ∈ S then sgn (x i) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]; rfl

lemma chi_mul {n : ℕ} (S T : Finset (Fin n)) : chi S * chi T = chi (symmDiff S T) := by
  funext x
  simp only [Pi.mul_apply, chi_apply_prod_univ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, sgn_mul_self]

lemma card_symmDiff_le {n : ℕ} (S T : Finset (Fin n)) :
    (symmDiff S T).card ≤ S.card + T.card :=
  le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
      (Finset.card_le_card Finset.sdiff_subset))

/-- The space of functions of degree at most `D`. -/
def V (n D : ℕ) : Submodule F (Inp n → F) :=
  Submodule.span F {f : Inp n → F | ∃ S : Finset (Fin n), S.card ≤ D ∧ chi S = f}

lemma chi_mem_V {n D : ℕ} {S : Finset (Fin n)} (h : S.card ≤ D) : chi S ∈ V n D :=
  Submodule.subset_span ⟨S, h, rfl⟩

lemma V_mono {n : ℕ} {a b : ℕ} (h : a ≤ b) : V n a ≤ V n b := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨S, hS, rfl⟩
  exact chi_mem_V (le_trans hS h)

lemma one_mem_V {n D : ℕ} : (1 : Inp n → F) ∈ V n D := by
  rw [← chi_empty]; exact chi_mem_V (by simp)

lemma const_mem_V {n D : ℕ} (a : F) : (fun _ : Inp n => a) ∈ V n D := by
  have : (fun _ : Inp n => a) = a • (1 : Inp n → F) := by funext x; simp
  rw [this]; exact Submodule.smul_mem _ _ one_mem_V

lemma V_mul {n a b : ℕ} {f g : Inp n → F} (hf : f ∈ V n a) (hg : g ∈ V n b) :
    f * g ∈ V n (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨T, hT, rfl⟩ := hg
          rw [chi_mul]
          exact chi_mem_V (le_trans (card_symmDiff_le S T) (Nat.add_le_add hS hT))
      | zero => simp
      | add g1 g2 _ _ ih1 ih2 => rw [mul_add]; exact Submodule.add_mem _ ih1 ih2
      | smul c g _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f1 f2 _ _ ih1 ih2 => rw [add_mul]; exact Submodule.add_mem _ ih1 ih2
  | smul c f _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

/-- The index set of monomials of degree at most `D`. -/
def gens (n D : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => S.card ≤ D)

lemma mem_gens {n D : ℕ} {S : Finset (Fin n)} : S ∈ gens n D ↔ S.card ≤ D := by simp [gens]

/-- Membership in `V n D` means being a linear combination of the monomials of degree `≤ D`. -/
lemma mem_V_iff {n D : ℕ} (f : Inp n → F) :
    f ∈ V n D ↔ ∃ c : Finset (Fin n) → F, ∀ x, f x = ∑ S ∈ gens n D, c S * chi S x := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨S, hS, rfl⟩ := hf
        refine ⟨fun T => if T = S then 1 else 0, fun x => ?_⟩
        rw [Finset.sum_eq_single S]
        · simp
        · intro T _ hT; simp [hT]
        · intro h; exact absurd (mem_gens.2 hS) h
    | zero => exact ⟨0, fun x => by simp⟩
    | add f g _ _ ihf ihg =>
        obtain ⟨cf, hcf⟩ := ihf; obtain ⟨cg, hcg⟩ := ihg
        exact ⟨cf + cg, fun x => by simp [hcf, hcg, add_mul, Finset.sum_add_distrib]⟩
    | smul a f _ ih =>
        obtain ⟨c, hc⟩ := ih
        exact ⟨a • c, fun x => by simp [hc, Finset.mul_sum, mul_assoc]⟩
  · rintro ⟨c, hc⟩
    have : f = ∑ S ∈ gens n D, c S • chi S := by funext x; rw [hc x]; simp
    rw [this]
    exact Submodule.sum_mem _ (fun S hS => Submodule.smul_mem _ _ (chi_mem_V (mem_gens.1 hS)))

/-- Every function on `n` bits has degree at most `n`. -/
lemma V_top {n : ℕ} (f : Inp n → F) : f ∈ V n n := by
  classical
  have hdelta : ∀ a : Inp n, (fun x => if x = a then (1 : F) else 0) ∈ V n n := by
    intro a
    have hg : ∀ x : Inp n, (∏ i : Fin n, (sgn (a i) * sgn (x i) + 1))
        = ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, (∏ i ∈ t, sgn (a i)) * chi t x := by
      intro x
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp [chi, Finset.prod_mul_distrib]
    have hval : ∀ x : Inp n, (if x = a then (1 : F) else 0)
        = (2 : F) ^ n * (∏ i : Fin n, (sgn (a i) * sgn (x i) + 1)) := by
      intro x
      by_cases hx : x = a
      · subst hx
        have h2 : ∀ i : Fin n, sgn (x i) * sgn (x i) + 1 = (2 : F) := by
          intro i; rw [sgn_mul_self]; decide
        simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h4 : ((2 : F) ^ n) * (2 : F) ^ n = 1 := by
          rw [← mul_pow, show (2 : F) * 2 = 1 from by decide, one_pow]
        simpa using h4.symm
      · obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
          by_contra h
          push_neg at h
          exact hx (funext h)
        have hz : (∏ i : Fin n, (sgn (a i) * sgn (x i) + 1)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
          cases hxi : x i <;> cases hai : a i <;> simp [hxi, hai] at hi ⊢ <;> decide
        rw [hz, if_neg hx, mul_zero]
    have hrepr : (fun x => if x = a then (1 : F) else 0)
        = (2 : F) ^ n •
          (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, (∏ i ∈ t, sgn (a i)) • chi t) := by
      funext x
      rw [hval x, hg x]
      simp
    rw [hrepr]
    refine Submodule.smul_mem _ _
      (Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (chi_mem_V ?_)))
    simpa using Finset.card_le_univ t
  have hsum : f = ∑ a : Inp n, f a • (fun x => if x = a then (1 : F) else 0) := by
    funext x; simp
  rw [hsum]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (hdelta a))

/-! ### Parity -/

/-- The parity function on `n` bits. -/
def parity (n : ℕ) (x : Inp n) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

/-- The full character equals `1 + parity` in the additive encoding. -/
lemma chi_univ_eq (n : ℕ) (x : Inp n) :
    chi Finset.univ x = 1 + bit (parity n x) := by
  classical
  have h1 : chi (Finset.univ : Finset (Fin n)) x
      = (-1 : F) ^ (Finset.univ.filter (fun i => x i = true)).card := by
    rw [chi, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => x i = true)
      (fun i => sgn (x i))]
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : F)) (fun i hi => by
        simp only [Finset.mem_filter] at hi
        simp [sgn, hi.2]),
      Finset.prod_congr rfl (s₂ := Finset.univ.filter (fun i => ¬ (x i = true)))
        (g := fun _ => (1 : F)) (fun i hi => by
        simp only [Finset.mem_filter] at hi
        simp [sgn, hi.2])]
    simp
  rw [h1, parity, bit]
  by_cases h : Odd (Finset.univ.filter (fun i => x i = true)).card
  · rw [Odd.neg_one_pow h]
    simp [h]
    decide
  · rw [Nat.not_odd_iff_even] at h
    rw [Even.neg_one_pow h]
    simp [Nat.not_odd_iff_even.2 h]

end CS

