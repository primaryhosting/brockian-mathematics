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

theorem mod_gate {q k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) ∈ LD F n ((q - 1) * D) ∧
      ∀ x ∉ E, ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) x
        = bv F (decide (¬ (q ∣ ((univ.filter (fun i => bl i x = true)).card)))) := by
  refine ⟨pow_mem_LD (Submodule.sum_mem _ fun i _ => hg i), ?_⟩
  intro x hx
  have : ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) x = (∑ i, g i x) ^ (q - 1) := by
    simp [Finset.sum_apply]
  rw [this]
  have hsum : (∑ i, g i x) = (((univ.filter (fun i => bl i x = true)).card : ℕ) : F) := by
    rw [← sum_bv (F := F)]
    exact Finset.sum_congr rfl fun i _ => hE x hx i
  rw [hsum, natCast_pow_char hq]
  by_cases h : q ∣ ((univ.filter (fun i => bl i x = true)).card) <;> simp [bv, h]

/-! ### The approximation theorem for circuits -/

/-- **Razborov–Smolensky approximation.**  Over a field of characteristic `q`, every
circuit of depth `d` and size `s` over the basis `{AND, OR, NOT, MOD q}` agrees with a
function of degree at most `(ℓ (q-1))^d` on all but at most `s · 2^n / 2^ℓ` inputs. -/
