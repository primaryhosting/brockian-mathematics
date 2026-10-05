/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

set_option grind.warning false

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma eigsp_eq_span {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) {s : ℝ} (hs : 0 < s) :
    eigsp ψ s = Submodule.span ℂ (Set.range fun i : {i : Fin r // lam i = s} =>
      ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)) := by
  obtain ⟨hpos, heo, hfo, hpsi⟩ := hd
  have he := (orthonormal_iff_coord e).mp heo
  have hs2 : ((s : ℂ)) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (by exact_mod_cast hs.ne' : (s : ℂ) ≠ 0)
  have key : ∀ (v : Fin m → ℂ) (p : Fin m), ∑ p', rho ψ p p' * v p'
      = ∑ i, ((lam i : ℂ) ^ 2) * (∑ p', conj (e i p') * v p') * e i p := by
    intro v p
    have hstep : ∀ p', rho ψ p p' * v p'
        = ∑ i, (((lam i : ℂ) ^ 2) * e i p * conj (e i p')) * v p' := by
      intro p'
      rw [rho_eq_of_schmidt ⟨hpos, heo, hfo, hpsi⟩ p p', Finset.sum_mul]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ p', (((lam i : ℂ) ^ 2) * e i p * conj (e i p')) * v p'
        = (((lam i : ℂ) ^ 2) * e i p) * (conj (e i p') * v p') := fun p' => by ring
    simp_rw [this]
    rw [← Finset.mul_sum]
    ring
  apply le_antisymm
  · intro v hv
    rw [mem_eigsp_iff] at hv
    set c : Fin r → ℂ := fun i => ∑ p', conj (e i p') * v p' with hcdef
    have hveq : ∀ p, ((s : ℂ)) ^ 2 * v p = ∑ i, ((lam i : ℂ) ^ 2) * c i * e i p := fun p => by
      rw [← hv p, key v p]
    have hcj : ∀ j, ((s : ℂ)) ^ 2 * c j = ((lam j : ℂ) ^ 2) * c j := by
      intro j
      have h1 : ∑ p, conj (e j p) * (((s : ℂ)) ^ 2 * v p)
          = ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p) :=
        Finset.sum_congr rfl fun p _ => by rw [hveq p]
      have h2 : ∑ p, conj (e j p) * (((s : ℂ)) ^ 2 * v p) = ((s : ℂ)) ^ 2 * c j := by
        rw [hcdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      have h3 : ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p)
          = ((lam j : ℂ) ^ 2) * c j := by
        have hswap : ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p)
            = ∑ i, ((lam i : ℂ) ^ 2) * c i * ∑ p, conj (e j p) * e i p := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
        rw [hswap]
        simp_rw [he j]
        simp
      rw [h2, h3] at h1
      exact h1
    have hcz : ∀ j, lam j ≠ s → c j = 0 := by
      intro j hj
      have hne : ((lam j : ℂ) ^ 2) - ((s : ℂ)) ^ 2 ≠ 0 := by
        have hreal : (lam j) ^ 2 - s ^ 2 ≠ 0 := by
          have h1 : lam j + s > 0 := by have := hpos j; linarith
          have h2 : lam j - s ≠ 0 := sub_ne_zero.mpr hj
          intro hcon
          have : (lam j - s) * (lam j + s) = 0 := by nlinarith [hcon]
          rcases mul_eq_zero.mp this with h | h
          · exact h2 h
          · linarith
        have : ((lam j : ℂ) ^ 2 - (s : ℂ) ^ 2) = (((lam j) ^ 2 - s ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this]
        exact_mod_cast hreal
      have := hcj j
      have : (((lam j : ℂ) ^ 2) - ((s : ℂ)) ^ 2) * c j = 0 := by linear_combination -this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · exact h
    have hsum : v = ∑ i : {i : Fin r // lam i = s}, c i •
        ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) := by
      funext p
      have hstep : ∑ i, ((lam i : ℂ) ^ 2) * c i * e i p
          = ((s : ℂ)) ^ 2 * ∑ i, (if lam i = s then c i * e i p else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : lam i = s
        · rw [if_pos h, h]; ring
        · rw [if_neg h, hcz i h]; ring
      have h4 : ((s : ℂ)) ^ 2 * v p
          = ((s : ℂ)) ^ 2 * ∑ i, (if lam i = s then c i * e i p else 0) := by
        rw [hveq p, hstep]
      have h5 : v p = ∑ i, (if lam i = s then c i * e i p else 0) :=
        mul_left_cancel₀ hs2 h4
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h5, ← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun i => lam i = s)
        (fun x => by simp) (fun i => c i * e i p)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_eigsp_iff]
    intro p
    rw [key]
    have : ∀ i, ((lam i : ℂ) ^ 2) * (∑ p', conj (e i p') * e j p') * e i p
        = ((lam i : ℂ) ^ 2) * (if i = j then (1 : ℂ) else 0) * e i p := by
      intro i; rw [he i j]
    simp_rw [this]
    simp [Finset.sum_ite_eq', j.2]

