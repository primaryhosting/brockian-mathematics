import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem AgreeDeg_eq_top {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (h : (Fin (2 * m + 1) → Bool) → F)
    (hhD : h ∈ Deg F (2 * m + 1) D) (hh : ∀ x ∈ A, h x = ymono ζ univ x) :
    AgreeDeg F A (m + D) = ⊤ := by
  have hne : (ζ - 1) ≠ 0 := sub_ne_zero.2 hζ1
  rw [eq_top_iff, ← Deg_top (F := F) (n := 2 * m + 1), Deg, Submodule.span_le]
  rintro f ⟨S, -, rfl⟩
  have hexp : (∏ i ∈ S, (yfun ζ i + (fun _ => (-1 : F))))
      = ∑ T ∈ S.powerset, (ymono ζ T) * (∏ _i ∈ S \ T, (fun _ => (-1 : F))) := by
    rw [Finset.prod_add]
    rfl
  have hmono : mono F S = ((ζ - 1)⁻¹) ^ S.card • (∏ i ∈ S, (yfun ζ i + (fun _ => (-1 : F)))) := by
    funext x
    simp only [Finset.prod_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hpt : ∀ i ∈ S, (yfun ζ i x + (-1 : F)) = (ζ - 1) * (if x i then (1 : F) else 0) := by
      intro i _
      simp only [yfun]
      cases hx : x i <;> simp; ring
    rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_const,
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hne, one_pow, one_mul]
    rfl
  rw [SetLike.mem_coe, hmono]
  refine Submodule.smul_mem _ _ ?_
  rw [hexp]
  refine Submodule.sum_mem _ (fun T _ => ?_)
  have h1 : (ymono ζ T) * (∏ _i ∈ S \ T, (fun _ => (-1 : F)))
      = ((-1 : F)) ^ (S \ T).card • (ymono ζ T) := by
    funext x
    simp [Finset.prod_const, mul_comm]
  rw [h1]
  exact Submodule.smul_mem _ _ (ymono_mem_AgreeDeg ζ hζ0 h hhD hh T)

/-- Smolensky's counting bound. -/
