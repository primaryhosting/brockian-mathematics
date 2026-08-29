import Mathlib
/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian

variable {n : ℕ} [NeZero n]

/-- The `k`-th character of the vertex set `ZMod n` of the regular `n`-gon:
`χ_k(j) = exp (2πi k j / n)`. -/
noncomputable def ngonChar (n : ℕ) [NeZero n] (k j : ZMod n) : ℂ :=
  ZMod.stdAddChar (k * j)

/-- Rotation of the `n`-gon acting on functions on its vertices. -/
def ngonRot (n : ℕ) (f : ZMod n → ℂ) : ZMod n → ℂ := fun j => f (j + 1)

/-- The reflection of the `n`-gon acting on functions on its vertices. -/
def ngonRefl (n : ℕ) (f : ZMod n → ℂ) : ZMod n → ℂ := fun j => f (-j)

/-- The projection onto the `k`-th isotypic component of the vertex representation. -/
noncomputable def ngonProj (n : ℕ) [NeZero n] (k : ZMod n) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j => (n : ℂ)⁻¹ * ∑ m : ZMod n, ngonChar n k (j - m) * f m

/-- The Fourier coefficient of `f` at the character `χ_k`. -/
noncomputable def ngonCoef (n : ℕ) [NeZero n] (k : ZMod n) (f : ZMod n → ℂ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ m : ZMod n, ngonChar n k (-m) * f m

lemma ngonChar_add (k a b : ZMod n) :
    ngonChar n k (a + b) = ngonChar n k a * ngonChar n k b := by
  unfold ngonChar
  rw [mul_add, AddChar.map_add_eq_mul]

lemma ngonChar_zero (k : ZMod n) : ngonChar n k 0 = 1 := by
  simp [ngonChar]

/-- Orthogonality relation: the character sum over all vertices vanishes unless `k = 0`. -/
lemma sum_ngonChar (k : ZMod n) :
    ∑ m : ZMod n, ngonChar n k m = if k = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod n) (ψ := ZMod.stdAddChar) k
    (ZMod.isPrimitive_stdAddChar n)
  simp only [ngonChar, mul_comm] at h ⊢
  rw [h]
  simp [ZMod.card]

/-- Dual orthogonality relation: the sum over all characters vanishes away from the origin. -/
lemma sum_ngonChar_index (j : ZMod n) :
    ∑ k : ZMod n, ngonChar n k j = if j = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod n) (ψ := ZMod.stdAddChar) j
    (ZMod.isPrimitive_stdAddChar n)
  simp only [ngonChar] at h ⊢
  rw [h]
  simp [ZMod.card]

/-- Each isotypic projection lands in the line spanned by the corresponding character. -/
lemma ngonProj_eq_smul_char (k : ZMod n) (f : ZMod n → ℂ) :
    ngonProj n k f = fun j => ngonCoef n k f * ngonChar n k j := by
  funext j
  simp only [ngonProj, ngonCoef]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : j - m = -m + j := by ring
  rw [h, ngonChar_add]
  ring

lemma ngonProj_const_smul (k : ZMod n) (c : ℂ) (f : ZMod n → ℂ) :
    ngonProj n k (fun j => c * f j) = fun j => c * ngonProj n k f j := by
  funext j
  simp only [ngonProj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma ngonProj_char (k l : ZMod n) :
    ngonProj n k (ngonChar n l) = if k = l then ngonChar n l else 0 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcoef : ngonCoef n k (ngonChar n l) = if k = l then 1 else 0 := by
    simp only [ngonCoef, ngonChar]
    have hm : ∀ m : ZMod n, ZMod.stdAddChar (k * -m) * ZMod.stdAddChar (l * m)
        = ZMod.stdAddChar ((l - k) * m) := by
      intro m
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    rw [Finset.sum_congr rfl fun m _ => hm m]
    have h2 := sum_ngonChar (n := n) (l - k)
    simp only [ngonChar] at h2
    rw [h2]
    by_cases h : k = l
    · simp [h, hn]
    · have hne : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      simp [hne, h]
  rw [ngonProj_eq_smul_char, hcoef]
  by_cases h : k = l
  · subst h; simp
  · simp only [h, if_false]
    funext j
    simp

lemma ngonProj_ngonProj (k l : ZMod n) (f : ZMod n → ℂ) :
    ngonProj n k (ngonProj n l f) = if k = l then ngonProj n l f else 0 := by
  rw [ngonProj_eq_smul_char l f,
    ngonProj_const_smul k (ngonCoef n l f) (ngonChar n l), ngonProj_char]
  by_cases h : k = l
  · subst h; simp
  · simp only [h, if_false]
    funext j
    simp

/-- Completeness: the isotypic projections sum to the identity. -/
lemma sum_ngonProj (f : ZMod n → ℂ) : ∑ k : ZMod n, ngonProj n k f = f := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  funext j
  rw [Finset.sum_apply]
  simp only [ngonProj]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ m : ZMod n, ∑ k : ZMod n, ngonChar n k (j - m) * f m
      = if m = j then (n : ℂ) * f j else 0 := by
    intro m
    rw [← Finset.sum_mul, sum_ngonChar_index]
    by_cases h : m = j
    · subst h; simp
    · have hne : j - m ≠ 0 := fun hc => h (sub_eq_zero.mp hc).symm
      simp [hne, h]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_ite_eq' Finset.univ j]
  simp [hn]

/-- The `k`-th isotypic component is a rotation eigenspace with eigenvalue `χ_k(1)`. -/
lemma ngonRot_ngonProj (k : ZMod n) (f : ZMod n → ℂ) :
    ngonRot n (ngonProj n k f) = fun j => ngonChar n k 1 * ngonProj n k f j := by
  funext j
  simp only [ngonRot, ngonProj_eq_smul_char, ngonChar_add]
  ring

/-- The reflection of the `n`-gon interchanges the `k`-th and `(-k)`-th isotypic components. -/
lemma ngonRefl_ngonProj (k : ZMod n) (f : ZMod n → ℂ) :
    ngonRefl n (ngonProj n k f) = ngonProj n (-k) (ngonRefl n f) := by
  funext j
  simp only [ngonRefl, ngonProj_eq_smul_char, ngonCoef, ngonChar]
  have hchar : ZMod.stdAddChar (k * -j) = ZMod.stdAddChar (-k * j) := by ring_nf
  rw [hchar]
  congr 1
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun m => ?_)
  simp only [Equiv.neg_apply, neg_neg]
  congr 2
  ring

/-- **Isotypic decomposition of the vertex representation of the regular `n`-gon.**

For every `n ≥ 1`, the space of complex functions on the vertices `ZMod n` of the regular
`n`-gon decomposes into the isotypic components of the dihedral group `D_n`, cut out by the
projections `ngonProj n k`.  The six conjuncts state, respectively:

* completeness: the projections sum to the identity;
* idempotence of each projection;
* orthogonality of distinct projections;
* each component is a rotation eigenspace with eigenvalue `χ_k(1)`;
* the reflection interchanges the `k`-th and `(-k)`-th components (so that
  `W_k ⊕ W_{-k}` is the `D_n`-isotypic plane);
* the projections act on characters as the expected Kronecker delta.

This generalizes the classical `D₅` pentagon statement (`n = 5`) to all `n`. -/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    (∑ k : ZMod n, ngonProj n k f) = f
      ∧ (∀ k : ZMod n, ngonProj n k (ngonProj n k f) = ngonProj n k f)
      ∧ (∀ k l : ZMod n, k ≠ l → ngonProj n k (ngonProj n l f) = 0)
      ∧ (∀ k : ZMod n, ngonRot n (ngonProj n k f)
            = fun j => ngonChar n k 1 * ngonProj n k f j)
      ∧ (∀ k : ZMod n, ngonRefl n (ngonProj n k f) = ngonProj n (-k) (ngonRefl n f))
      ∧ (∀ k l : ZMod n, ngonProj n k (ngonChar n l) = if k = l then ngonChar n l else 0) := by
  refine ⟨sum_ngonProj f, ?_, ?_, fun k => ngonRot_ngonProj k f,
    fun k => ngonRefl_ngonProj k f, fun k l => ngonProj_char k l⟩
  · intro k
    simpa using ngonProj_ngonProj k k f
  · intro k l hkl
    simpa [hkl] using ngonProj_ngonProj k l f

/-- The classical pentagon (`D₅`) case: the five-dimensional vertex representation splits as
the trivial component together with the two two-dimensional isotypic planes
`W₁ = ⟨χ₁, χ₄⟩` and `W₂ = ⟨χ₂, χ₃⟩`, each of which is stable under the reflection. -/
theorem pentagon_isotypic_decomposition (f : ZMod 5 → ℂ) :
    f = ngonProj 5 0 f + (ngonProj 5 1 f + ngonProj 5 4 f)
          + (ngonProj 5 2 f + ngonProj 5 3 f)
      ∧ ngonRefl 5 (ngonProj 5 1 f + ngonProj 5 4 f)
          = ngonProj 5 4 (ngonRefl 5 f) + ngonProj 5 1 (ngonRefl 5 f)
      ∧ ngonRefl 5 (ngonProj 5 2 f + ngonProj 5 3 f)
          = ngonProj 5 3 (ngonRefl 5 f) + ngonProj 5 2 (ngonRefl 5 f) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := sum_ngonProj (n := 5) f
    rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide] at h
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
    linear_combination (norm := abel) -h
  · have h1 := ngonRefl_ngonProj (n := 5) 1 f
    have h4 := ngonRefl_ngonProj (n := 5) 4 f
    rw [show (-1 : ZMod 5) = 4 from by decide] at h1
    rw [show (-4 : ZMod 5) = 1 from by decide] at h4
    have hadd : ngonRefl 5 (ngonProj 5 1 f + ngonProj 5 4 f)
        = ngonRefl 5 (ngonProj 5 1 f) + ngonRefl 5 (ngonProj 5 4 f) := rfl
    rw [hadd, h1, h4]
  · have h2 := ngonRefl_ngonProj (n := 5) 2 f
    have h3 := ngonRefl_ngonProj (n := 5) 3 f
    rw [show (-2 : ZMod 5) = 3 from by decide] at h2
    rw [show (-3 : ZMod 5) = 2 from by decide] at h3
    have hadd : ngonRefl 5 (ngonProj 5 2 f + ngonProj 5 3 f)
        = ngonRefl 5 (ngonProj 5 2 f) + ngonRefl 5 (ngonProj 5 3 f) := rfl
    rw [hadd, h2, h3]

end Brockian

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

