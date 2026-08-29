import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem and_gate {q ℓ k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ∃ f ∈ LD F n (ℓ * ((q - 1) * D)),
      2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
          (fun x => f x ≠ bv F (decide (∀ i, bl i x = true)))).card
        ≤ 2 ^ ℓ * E.card + 2 ^ n := by
  classical
  have hg' : ∀ i, (1 - g i : (Fin n → Bool) → F) ∈ LD F n D :=
    fun i => Submodule.sub_mem _ (one_mem_LD _) (hg i)
  have hE' : ∀ x ∉ E, ∀ i, (1 - g i : (Fin n → Bool) → F) x = bv F ((!bl i x)) := by
    intro x hx i
    simp only [Pi.sub_apply, Pi.one_apply, hE x hx i, bv_not]
  obtain ⟨f₀, hf₀mem, hf₀⟩ := or_gate (ℓ := ℓ) hq (fun i => 1 - g i) hg'
    (fun i x => !(bl i x)) E hE'
  refine ⟨1 - f₀, Submodule.sub_mem _ (one_mem_LD _) hf₀mem, ?_⟩
  have hset : ((univ : Finset (Fin n → Bool)).filter
      (fun x => (1 - f₀ : (Fin n → Bool) → F) x ≠ bv F (decide (∀ i, bl i x = true))))
      = ((univ : Finset (Fin n → Bool)).filter
      (fun x => f₀ x ≠ bv F (decide (∃ i, (!bl i x) = true)))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.one_apply]
    have hb : bv F (decide (∀ i, bl i x = true)) = 1 - bv F (decide (∃ i, (!bl i x) = true)) := by
      by_cases h : ∀ i, bl i x = true
      · have h1 : ¬ ∃ i, bl i x = false := by
          push_neg
          intro i
          simp [h i]
        simp [bv, h, h1]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have h1 : ∃ i, bl i x = false := ⟨i, Bool.eq_false_iff.mpr hi⟩
        have h2 : ¬ ∀ i, bl i x = true := by push_neg; exact ⟨i, hi⟩
        simp [bv, h1, h2]
    rw [hb]
    constructor
    · intro h hc; exact h (by rw [hc])
    · intro h hc; exact h (by linear_combination -hc)
  rw [hset]
  exact hf₀

/-- A `MOD q` gate is computed *exactly* by a function of degree `q - 1`. -/
