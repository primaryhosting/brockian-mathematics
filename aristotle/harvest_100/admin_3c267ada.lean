import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace CS

/-- The field with three elements. -/
abbrev F3 := ZMod 3

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `±1` encoding of a Boolean value inside `F3`. -/
def sgn (b : Bool) : F3 := if b then -1 else 1

/-- `0/1` encoding of a Boolean value inside `F3`. -/
def enc (b : Bool) : F3 := if b then 1 else 0

@[simp] lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

/-- The monomial function `x ↦ ∏_{i ∈ A} sgn (x i)`. -/
def mono {n : ℕ} (A : Finset (Fin n)) : Cube n → F3 := fun x => ∏ i ∈ A, sgn (x i)

@[simp] lemma mono_empty {n : ℕ} : mono (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

lemma mono_mul {n : ℕ} (A B : Finset (Fin n)) :
    mono A * mono B = mono (symmDiff A B) := by
  funext x
  have hA : (∏ i ∈ A, sgn (x i)) = (∏ i ∈ A \ B, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) := by
    rw [← Finset.prod_sdiff (show A ∩ B ⊆ A from Finset.inter_subset_left)]
    congr 1
    · congr 1
      ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
      tauto
  have hB : (∏ i ∈ B, sgn (x i)) = (∏ i ∈ B \ A, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) := by
    rw [← Finset.prod_sdiff (show A ∩ B ⊆ B from Finset.inter_subset_right)]
    congr 1
    · congr 1
      ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
      tauto
  have hsq : (∏ i ∈ A ∩ B, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp [Finset.mem_sdiff] at ha hb
    exact hb.2 ha.1
  have hsymm : symmDiff A B = (A \ B) ∪ (B \ A) := rfl
  have hsq2 : (∏ i ∈ A ∩ B, sgn (x i)) ^ 2 = 1 := by rw [sq]; exact hsq
  simp only [Pi.mul_apply, mono, hA, hB, hsymm, Finset.prod_union hdisj]
  ring_nf
  rw [hsq2]
  ring

/-- The `F3`-submodule of functions on the cube spanned by monomials of degree at most `D`. -/
def Deg (n D : ℕ) : Submodule F3 (Cube n → F3) :=
  Submodule.span F3 {f | ∃ A : Finset (Fin n), A.card ≤ D ∧ f = mono A}

lemma mono_mem_Deg {n D : ℕ} {A : Finset (Fin n)} (h : A.card ≤ D) : mono A ∈ Deg n D :=
  Submodule.subset_span ⟨A, h, rfl⟩

lemma Deg_mono {n : ℕ} {D E : ℕ} (h : D ≤ E) : Deg n D ≤ Deg n E := by
  apply Submodule.span_le.2
  rintro f ⟨A, hA, rfl⟩
  exact mono_mem_Deg (hA.trans h)

lemma one_mem_Deg {n D : ℕ} : (1 : Cube n → F3) ∈ Deg n D := by
  have := mono_mem_Deg (A := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma const_mem_Deg {n D : ℕ} (c : F3) : (fun _ => c : Cube n → F3) ∈ Deg n D := by
  have : (fun _ => c : Cube n → F3) = c • (1 : Cube n → F3) := by
    funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ one_mem_Deg

lemma mul_mem_Deg {n a b : ℕ} {f g : Cube n → F3} (hf : f ∈ Deg n a) (hg : g ∈ Deg n b) :
    f * g ∈ Deg n (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨A, hA, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨B, hB, rfl⟩ := hg
          rw [mono_mul]
          refine mono_mem_Deg ?_
          calc (symmDiff A B).card ≤ (A ∪ B).card := by
                apply Finset.card_le_card
                intro i hi
                simp only [Finset.mem_union]
                have : i ∈ A \ B ∪ B \ A := hi
                simp [Finset.mem_union, Finset.mem_sdiff] at this
                tauto
            _ ≤ A.card + B.card := Finset.card_union_le _ _
            _ ≤ a + b := Nat.add_le_add hA hB
      | zero => simpa using Submodule.zero_mem _
      | add g1 g2 _ _ ih1 ih2 =>
          rw [mul_add]; exact Submodule.add_mem _ ih1 ih2
      | smul c g _ ih =>
          have : mono A * (c • g) = c • (mono A * g) := by
            funext x; simp [mul_comm, mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ _ ih
  | zero => simpa using Submodule.zero_mem _
  | add f1 f2 _ _ ih1 ih2 => rw [add_mul]; exact Submodule.add_mem _ ih1 ih2
  | smul c f _ ih =>
      have : (c • f) * g = c • (f * g) := by funext x; simp [mul_assoc]
      rw [this]; exact Submodule.smul_mem _ _ ih

/-- Every function on the cube is a combination of monomials of degree at most `n`. -/
lemma Deg_top (n : ℕ) : Deg n n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  -- write `f` as a combination of point indicators
  have hdelta : ∀ z : Cube n, (fun x => (2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
      ∈ Deg n n := by
    intro z
    have hexp : (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
            (∏ i ∈ Finset.univ \ A, sgn (z i)) • mono (Finset.univ \ A) := by
      funext x
      rw [Finset.prod_add, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro A _
      simp only [mono, Pi.smul_apply, smul_eq_mul, Finset.prod_const_one, one_mul]
      rw [← Finset.prod_mul_distrib]
    have h1 : (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i))) ∈ Deg n n := by
      rw [hexp]
      refine Submodule.sum_mem _ ?_
      intro A _
      exact Submodule.smul_mem _ _ (mono_mem_Deg (by
        simpa using Finset.card_le_univ (Finset.univ \ A)))
    have h2 : (fun x : Cube n => (2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = ((2 : F3)^n) • (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i))) := by
      funext x; simp
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have key : f = ∑ z : Cube n, f z • (fun x => (2 : F3)^n * ∏ i : Fin n,
      (1 + sgn (z i) * sgn (x i))) := by
    funext x
    rw [Finset.sum_apply]
    have hz : ∀ z : Cube n, ((2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = if z = x then 1 else 0 := by
      intro z
      by_cases h : z = x
      · subst h
        have : ∀ i : Fin n, (1 : F3) + sgn (z i) * sgn (z i) = 2 := by
          intro i; rw [sgn_mul_self]; ring
        simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, if_pos]
        rw [← mul_pow]
        have h22 : (2 : F3) * 2 = 1 := by decide
        rw [h22, one_pow]
        simp
      · have : ∃ i, z i ≠ x i := by
          by_contra hc
          push_neg at hc
          exact h (funext hc)
        obtain ⟨i, hi⟩ := this
        have hzero : (1 : F3) + sgn (z i) * sgn (x i) = 0 := by
          cases hz' : z i <;> cases hx' : x i <;> simp [hz', hx'] at hi ⊢ <;> simp [sgn] <;> decide
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
        simp [h]
    simp only [Pi.smul_apply, smul_eq_mul, hz]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [key]
  exact Submodule.sum_mem _ (fun z _ => Submodule.smul_mem _ _ (hdelta z))

end CS

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

