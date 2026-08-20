/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem eigenspace_eq_span {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) {t : ℝ} (ht : 0 < t) :
    Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2) =
      Submodule.span ℂ (Set.range (fun k : {k : Fin r // σ k = t} => u k.1)) := by
  classical
  have hon : ∀ k l, cdot (u k) (u l) = if k = l then 1 else 0 := h.onu
  have ht2 : ((t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ne_of_gt ht)
  have hmem : ∀ w : Fin m → ℂ,
      w ∈ Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2)
        ↔ ∀ i, (rho ψ *ᵥ w) i = (t : ℂ) ^ 2 * w i := by
    intro w
    rw [Module.End.mem_eigenspace_iff]
    constructor
    · intro hw i
      have := congrFun hw i
      simpa [Matrix.mulVecLin_apply] using this
    · intro hw
      funext i
      simpa [Matrix.mulVecLin_apply] using hw i
  apply le_antisymm
  · intro w hw
    rw [hmem] at hw
    set S : Finset (Fin r) := Finset.univ.filter (fun k => σ k = t) with hS
    have hmemS : ∀ x : Fin r, x ∈ S ↔ σ x = t := by
      intro x; simp [hS]
    have hc : ∀ l : Fin r, ((σ l : ℂ)) ^ 2 * cdot (u l) w = (t : ℂ) ^ 2 * cdot (u l) w := by
      intro l
      have hfun : (fun i => ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i)
          = (fun i => (t : ℂ) ^ 2 * w i) := by
        funext i
        rw [← hw i, rho_mulVec_of_isSchmidt h w i]
      have hh := congrArg (cdot (u l)) hfun
      rw [cdot_sum (u l) (fun k => ((σ k : ℂ)) ^ 2 * cdot (u k) w) u, cdot_smul] at hh
      simpa [hon, Finset.sum_ite_eq'] using hh
    have hzero : ∀ l : Fin r, σ l ≠ t → cdot (u l) w = 0 := by
      intro l hl
      have h1 := hc l
      have h2 : ((σ l : ℂ)) ^ 2 - (t : ℂ) ^ 2 ≠ 0 := by
        have hsum : σ l + t ≠ 0 := ne_of_gt (by have := h.pos l; linarith)
        have hmul : ((σ l : ℂ) - t) * ((σ l : ℂ) + t) ≠ 0 := by
          refine mul_ne_zero ?_ ?_
          · exact_mod_cast sub_ne_zero_of_ne hl
          · exact_mod_cast hsum
        intro hcon
        exact hmul (by linear_combination hcon)
      have hprod : (((σ l : ℂ)) ^ 2 - (t : ℂ) ^ 2) * cdot (u l) w = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 hprod with h' | h'
      · exact absurd h' h2
      · exact h'
    have hw' : ∀ i, w i = ∑ k ∈ S, cdot (u k) w * u k i := by
      intro i
      have e1 : (t : ℂ) ^ 2 * w i = ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i := by
        rw [← hw i, rho_mulVec_of_isSchmidt h w i]
      have e2 : ∑ k ∈ S, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i
          = ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i := by
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro x _ hx
        have hxt : σ x ≠ t := fun hcon => hx ((hmemS x).2 hcon)
        simp [hzero x hxt]
      have e3 : ∑ k ∈ S, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i
          = (t : ℂ) ^ 2 * ∑ k ∈ S, cdot (u k) w * u k i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [(hmemS k).1 hk]
        ring
      exact mul_left_cancel₀ ht2 (e1.trans (e2.symm.trans e3))
    have hrepr : w = ∑ k : {k : Fin r // σ k = t}, cdot (u k.1) w • u k.1 := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hw' i]
      exact Finset.sum_subtype S (p := fun k => σ k = t) hmemS
        (fun k => cdot (u k) w * u k i)
    rw [hrepr]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hmem]
    intro i
    rw [rho_mulVec_of_isSchmidt h (u k.1) i]
    have hterm : ∀ l : Fin r, ((σ l : ℂ)) ^ 2 * cdot (u l) (u k.1) * u l i
        = if l = k.1 then ((σ l : ℂ)) ^ 2 * u l i else 0 := by
      intro l
      rw [hon l k.1]
      by_cases hlk : l = k.1 <;> simp [hlk]
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_ite_eq' Finset.univ k.1]
    simp [k.2]

/-- The number of Schmidt coefficients equal to `t > 0` is the dimension of the `t ^ 2`
eigenspace of the reduced density matrix; in particular it does not depend on the
decomposition. -/
