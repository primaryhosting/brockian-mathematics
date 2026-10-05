/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/

lemma arrow_step {r : V → V → Prop} (hsymm : ∀ x y, r x y → r y x) {S : Finset V}
    {p q n₁ n₂ : ℕ}
    (hA : ∀ T : Finset V, n₁ ≤ T.card → Arrow r T p (q + 1))
    (hB : ∀ T : Finset V, n₂ ≤ T.card → Arrow r T (p + 1) q)
    (hne : S.Nonempty) (hS : n₁ + n₂ ≤ S.card) : Arrow r S (p + 1) (q + 1) := by
  classical
  obtain ⟨v, hv⟩ := hne
  set T := S.erase v with hT
  set A := T.filter (fun u => r v u) with hAdef
  set B := T.filter (fun u => ¬ r v u) with hBdef
  have hsum : A.card + B.card = T.card := Finset.card_filter_add_card_filter_not _
  have hTc : T.card + 1 = S.card := by
    rw [hT, Finset.card_erase_of_mem hv]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have hAT : A ⊆ T := Finset.filter_subset _ _
  have hBT : B ⊆ T := Finset.filter_subset _ _
  have hTS : T ⊆ S := Finset.erase_subset _ _
  have hcase : n₁ ≤ A.card ∨ n₂ ≤ B.card := by omega
  rcases hcase with hc | hc
  · rcases hA A hc with ⟨t, hts, hcard, hh⟩ | ⟨t, hts, hcard, hh⟩
    · have hvt : v ∉ t := fun hvt => (Finset.notMem_erase v S) (hAT (hts hvt))
      refine Or.inl ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hTS (hAT (hts h))
      · rw [Finset.card_insert_of_notMem hvt, hcard]
      · exact homog_insert hsymm hh (fun u hu => (Finset.mem_filter.mp (hts hu)).2)
    · exact Or.inr ⟨t, fun x hx => hTS (hAT (hts hx)), hcard, hh⟩
  · rcases hB B hc with ⟨t, hts, hcard, hh⟩ | ⟨t, hts, hcard, hh⟩
    · exact Or.inl ⟨t, fun x hx => hTS (hBT (hts hx)), hcard, hh⟩
    · have hvt : v ∉ t := fun hvt => (Finset.notMem_erase v S) (hBT (hts hvt))
      refine Or.inr ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hTS (hBT (hts h))
      · rw [Finset.card_insert_of_notMem hvt, hcard]
      · exact homog_insert (fun _ _ h hcon => h (hsymm _ _ hcon)) hh
          (fun u hu => (Finset.mem_filter.mp (hts hu)).2)

/-- `R(3,3) ≤ 6`. -/
