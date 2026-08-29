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

lemma exists_or_approx {k ℓ : ℕ} (hq : q.Prime) [CharP F q] (u : Fin k → Cube n → F)
    (b : Fin k → Cube n → Bool) (Bad : Finset (Cube n))
    (hgood : ∀ x, x ∉ Bad → ∀ i, u i x = boolF F (b i x)) :
    ∃ ω : Fin ℓ → Fin k → Bool,
      (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ
        ≤ Bad.card * 2 ^ ℓ + 2 ^ n := by
  classical
  set Ω := (Finset.univ : Finset (Fin ℓ → Fin k → Bool)) with hΩ
  set bad : (Fin ℓ → Fin k → Bool) → Cube n → Prop := fun ω x =>
    orPoly q ω u x ≠ boolF F (decide (∃ i, b i x = true)) with hbad
  have hcardΩ : Ω.card = 2 ^ (k * ℓ) := by
    simp only [hΩ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      pow_mul]
  have hsplit : ∀ ω : Fin ℓ → Fin k → Bool,
      (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card
        ≤ Bad.card + #{x ∈ Finset.univ \ Bad | bad ω x} := by
    intro ω
    have hs : errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))
        ⊆ Bad ∪ {x ∈ Finset.univ \ Bad | bad ω x} := by
      intro x hx
      by_cases hxB : x ∈ Bad
      · exact Finset.mem_union_left _ hxB
      · refine Finset.mem_union_right _ ?_
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨hxB, mem_errSet.1 hx⟩
    exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
  have hswap : ∑ ω ∈ Ω, #{x ∈ Finset.univ \ Bad | bad ω x}
      = ∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hpt : ∀ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ ≤ 2 ^ (k * ℓ) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    refine card_bad_omega_le hq u b x (hgood x hx) _ ?_
    intro ω hω
    simp only [Finset.mem_filter] at hω
    exact hω.2
  have hsum : (∑ ω ∈ Ω, (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ)
      ≤ ∑ _ω ∈ Ω, (Bad.card * 2 ^ ℓ + 2 ^ n) := by
    have h1 : (∑ ω ∈ Ω, (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card
          * 2 ^ ℓ)
        ≤ ∑ ω ∈ Ω, (Bad.card * 2 ^ ℓ + #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ) := by
      refine Finset.sum_le_sum fun ω _ => ?_
      calc (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ
          ≤ (Bad.card + #{x ∈ Finset.univ \ Bad | bad ω x}) * 2 ^ ℓ :=
            Nat.mul_le_mul_right _ (hsplit ω)
        _ = Bad.card * 2 ^ ℓ + #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ := by ring
    refine le_trans h1 ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine Nat.add_le_add_left ?_ _
    have h2 : ∑ ω ∈ Ω, #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ
        = (∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hswap]
    rw [h2]
    calc (∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ)
        ≤ ∑ _x ∈ Finset.univ \ Bad, 2 ^ (k * ℓ) := Finset.sum_le_sum hpt
      _ ≤ ∑ _x ∈ (Finset.univ : Finset (Cube n)), 2 ^ (k * ℓ) :=
          Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
      _ = 2 ^ n * 2 ^ (k * ℓ) := by
          simp [Finset.sum_const, Fintype.card_fun]
      _ = ∑ _ω ∈ Ω, 2 ^ n := by rw [Finset.sum_const, hcardΩ, smul_eq_mul, mul_comm]
  have hne : Ω.Nonempty := ⟨fun _ _ => false, Finset.mem_univ _⟩
  obtain ⟨ω, -, hω⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨ω, hω⟩

/-- **The approximation lemma.**  Every circuit of depth `d` and size `s` over
`{¬, ∧, ∨, MOD q}` is approximated, over a field of characteristic `q`, by a function of
degree at most `(ℓ (q-1))^d` which errs on at most `s · 2^n / 2^ℓ` inputs. -/
