/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem span_schmidt_eq_eigSp {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) {t : ℝ} (ht : 0 < t) :
    Submodule.span ℂ (Set.range (fun k : {k : Fin r // s k = t} => u k.val))
      = eigSp (reduced psi) ((t : ℂ) ^ 2) := by
  have hs := h.1
  have hu : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := h.2.1
  have htne : ((t : ℂ)) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨k, rfl⟩
    have := reduced_eigenvector h k.val
    rw [k.property] at this
    exact this
  · intro x hx
    rw [mem_eigSp_iff] at hx
    set c : Fin r → ℂ := fun k => ∑ i', conj (u k i') * x i' with hcdef
    have hxi : ∀ i, ((t : ℂ) ^ 2) * x i = ∑ k, ((s k : ℂ) ^ 2 * c k) * u k i := by
      intro i
      rw [← hx i, reduced_apply h x i]
    -- the coefficients `c l` vanish unless `s l = t`
    have hcl : ∀ l, ((t : ℂ) ^ 2) * c l = ((s l : ℂ) ^ 2) * c l := by
      intro l
      have e1 : ((t : ℂ) ^ 2) * c l = ∑ i, conj (u l i) * (((t : ℂ) ^ 2) * x i) := by
        rw [hcdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1]
      have e2 : ∀ i : A, conj (u l i) * (∑ k, ((s k : ℂ) ^ 2 * c k) * u k i)
          = ∑ k, ((s k : ℂ) ^ 2 * c k) * (conj (u l i) * u k i) := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      calc ∑ i, conj (u l i) * (((t : ℂ) ^ 2) * x i)
          = ∑ i, conj (u l i) * (∑ k, ((s k : ℂ) ^ 2 * c k) * u k i) := by
            exact Finset.sum_congr rfl fun i _ => by rw [hxi i]
        _ = ∑ k, ((s k : ℂ) ^ 2 * c k) * ∑ i, conj (u l i) * u k i := by
            simp only [e2]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
        _ = ((s l : ℂ) ^ 2) * c l := by
            simp only [hu]
            simp
    have hzero : ∀ l, s l ≠ t → c l = 0 := by
      intro l hl
      have h1 : (((t : ℂ) ^ 2) - ((s l : ℂ) ^ 2)) * c l = 0 := by
        have := hcl l; ring_nf; ring_nf at this; linear_combination this
      have h2 : (((t : ℂ) ^ 2) - ((s l : ℂ) ^ 2)) ≠ 0 := by
        have : (t : ℝ) ^ 2 - (s l) ^ 2 ≠ 0 := by
          have hpos := hs l
          intro hcon
          apply hl
          nlinarith [sq_nonneg (t - s l), sq_nonneg (t + s l)]
        intro hcon
        apply this
        have : ((((t : ℝ) ^ 2 - (s l) ^ 2 : ℝ)) : ℂ) = 0 := by push_cast; linear_combination hcon
        exact_mod_cast this
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hx_eq : ∀ i, x i = ∑ k : {k : Fin r // s k = t}, c k.val * u k.val i := by
      intro i
      have e3 : ∑ k, ((s k : ℂ) ^ 2 * c k) * u k i
          = ∑ k, ((t : ℂ) ^ 2) * ((if s k = t then c k else 0) * u k i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : s k = t
        · simp [hk]; ring
        · simp [hk, hzero k hk]
      have e4 : ((t : ℂ) ^ 2) * x i
          = ((t : ℂ) ^ 2) * ∑ k, (if s k = t then c k else 0) * u k i := by
        rw [hxi i, e3, ← Finset.mul_sum]
      have e5 : x i = ∑ k, (if s k = t then c k else 0) * u k i :=
        mul_left_cancel₀ htne e4
      rw [e5]
      rw [← Finset.sum_subtype (Finset.univ.filter (fun k => s k = t))
        (by intro k; simp) (fun k => c k * u k i)]
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun k _ => by by_cases hk : s k = t <;> simp [hk]
    have : x = ∑ k : {k : Fin r // s k = t}, c k.val • u k.val := by
      funext i
      rw [hx_eq i]
      simp
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨k, rfl⟩

omit [DecidableEq B] in
