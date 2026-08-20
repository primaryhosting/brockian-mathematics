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

lemma exists_sep_set {n : ℕ} : ∀ (k : ℕ) (Ws : Submodule F (V n → F)), Module.finrank F Ws = k →
    ∃ U : Finset (V n), U.card ≤ k ∧ ∀ P ∈ Ws, (∀ u ∈ U, P u = 0) → P = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Ws hrank
    by_cases hbot : Ws = ⊥
    · refine ⟨∅, by simp, fun P hP _ => ?_⟩
      rw [hbot, Submodule.mem_bot] at hP; exact hP
    · obtain ⟨P₀, hP₀mem, hP₀ne⟩ : ∃ P₀ ∈ Ws, P₀ ≠ 0 := by
        have hbot' : Ws ≠ ⊥ := hbot
        rw [Submodule.ne_bot_iff] at hbot'
        obtain ⟨P₀, h1, h2⟩ := hbot'; exact ⟨P₀, h1, h2⟩
      obtain ⟨v, hv⟩ : ∃ v, P₀ v ≠ 0 := Function.ne_iff.1 hP₀ne
      set Kv : Submodule F (V n → F) :=
        LinearMap.ker (LinearMap.proj v : (V n → F) →ₗ[F] F)
      have hlt : Ws ⊓ Kv < Ws := by
        refine lt_of_le_of_ne inf_le_left (fun heq => hv ?_)
        have hmem : P₀ ∈ Ws ⊓ Kv := by rw [heq]; exact hP₀mem
        exact hmem.2
      have hk' : Module.finrank F (Ws ⊓ Kv : Submodule F (V n → F)) < k := by
        rw [← hrank]; exact Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨U', hcard', hsep'⟩ := ih _ hk' (Ws ⊓ Kv) rfl
      refine ⟨insert v U', ?_, ?_⟩
      · have := Finset.card_insert_le v U'
        omega
      · intro P hP hzero
        exact hsep' P ⟨hP, hzero v (Finset.mem_insert_self v U')⟩
          (fun u hu => hzero u (Finset.mem_insert_of_mem hu))

/-- A subspace of functions contains an element whose support has size at least the dimension. -/
