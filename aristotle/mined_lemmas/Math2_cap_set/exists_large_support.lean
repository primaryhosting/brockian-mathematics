/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

lemma exists_large_support {n : ℕ} (Ws : Submodule F (V n → F)) :
    ∃ P ∈ Ws, Module.finrank F Ws ≤ (Finset.univ.filter (fun x : V n => P x ≠ 0)).card := by
  classical
  obtain ⟨U, hcard, hsep⟩ := exists_sep_set (Module.finrank F Ws) Ws rfl
  set r : Ws →ₗ[F] ({u : V n // u ∈ U} → F) :=
    { toFun := fun P u => (P : V n → F) (u : V n)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } with hr
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have hz : (P : V n → F) = 0 := hsep _ P.2 (fun u hu => congrFun hP ⟨u, hu⟩)
    exact Subtype.ext hz
  have hfr : Module.finrank F ({u : V n // u ∈ U} → F) = U.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hle : Module.finrank F Ws ≤ U.card := by
    have := LinearMap.finrank_le_finrank_of_injective (f := r) hinj
    rwa [hfr] at this
  have heq : Module.finrank F Ws = Module.finrank F ({u : V n // u ∈ U} → F) := by
    rw [hfr]; omega
  have hsurj : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  obtain ⟨P, hP⟩ := hsurj 1
  refine ⟨(P : V n → F), P.2, ?_⟩
  have hsub : U ⊆ Finset.univ.filter (fun x : V n => (P : V n → F) x ≠ 0) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (P : V n → F) u = 1 := congrFun hP ⟨u, hu⟩
    rw [h1]; exact one_ne_zero
  calc Module.finrank F Ws ≤ U.card := hle
    _ ≤ _ := Finset.card_le_card hsub

end Support

section Main

/-- The flip map on exponent vectors, `a ↦ 2 - a`. -/
