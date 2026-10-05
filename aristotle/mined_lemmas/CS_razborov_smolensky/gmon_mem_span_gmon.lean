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
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma gmon_mem_span_gmon (a b : Fin n → F) (hab : ∀ i, a i ≠ b i) (a' b' : Fin n → F)
    (A : Finset (Fin n)) :
    gmon F a' b' A ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ A, f = gmon F a b B} := by
  classical
  induction A using Finset.induction with
  | empty =>
    have h0 : gmon F a' b' ∅ = gmon F a b ∅ := by rw [gmon_empty, gmon_empty]
    rw [h0]
    exact Submodule.subset_span ⟨∅, by simp, rfl⟩
  | insert j A hj ih =>
    set w : Cube n → F := fun x => if x j then b' j else a' j with hwdef
    have hne : b j - a j ≠ 0 := sub_ne_zero.2 (hab j).symm
    obtain ⟨β, hbeta⟩ : ∃ β : F, β * (b j - a j) = b' j - a' j :=
      ⟨(b' j - a' j) / (b j - a j), div_mul_cancel₀ _ hne⟩
    have hw : ∀ x : Cube n, w x = (a' j - β * a j) + β * (if x j then b j else a j) := by
      intro x
      cases h : x j
      · simp only [hwdef, h, Bool.false_eq_true, if_false]
        ring
      · simp only [hwdef, h, if_true]
        linear_combination -hbeta
    have hfac : gmon F a' b' (insert j A) = w * gmon F a' b' A := by
      funext x
      simp [gmon, Finset.prod_insert hj, hwdef]
    have main : ∀ g ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ A, f = gmon F a b B},
        w * g ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ insert j A, f = gmon F a b B} := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨B, hBA, rfl⟩ := hf
        have hjB : j ∉ B := fun h => hj (hBA h)
        have hsplit : w * gmon F a b B
            = (a' j - β * a j) • gmon F a b B + β • gmon F a b (insert j B) := by
          funext x
          simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, gmon,
            Finset.prod_insert hjB, hw x]
          ring
        rw [hsplit]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨B, hBA.trans (Finset.subset_insert _ _), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨insert j B, Finset.insert_subset_insert _ hBA, rfl⟩))
      | zero => simp
      | add u v _ _ ihu ihv => rw [mul_add]; exact Submodule.add_mem _ ihu ihv
      | smul c v _ ih' => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih'
    rw [hfac]
    exact main _ ih

/-- Any product of single-coordinate functions over `A` has degree at most `#A`. -/
