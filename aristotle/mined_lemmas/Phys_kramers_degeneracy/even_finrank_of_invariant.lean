/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space `V`: an antiunitary
(antilinear, inner-product-conjugating) involution-up-to-sign with `Θ ∘ Θ = -1`,
which is the situation of a half-integer-spin system. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  /-- Additivity. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Antilinearity. -/
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- Antiunitarity: `⟪Θ x, Θ y⟫ = conj ⟪x, y⟫ = ⟪y, x⟫`. -/
  inner_map' : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- Half-integer spin: `Θ² = -1`. -/
  sq_eq_neg' : ∀ x, toFun (toFun x) = -x

namespace TimeReversal

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

variable (Θ : TimeReversal V)


lemma even_finrank_of_invariant [FiniteDimensional ℂ V] :
    ∀ n : ℕ, ∀ U : Submodule ℂ V, Module.finrank ℂ U = n → (∀ x ∈ U, Θ x ∈ U) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hUrank hinv
    rcases eq_or_ne n 0 with h0 | h0
    · simp [h0]
    have hUne : U ≠ ⊥ := by
      rintro rfl
      simp at hUrank
      exact h0 hUrank.symm
    obtain ⟨ψ, hψU, hψ0⟩ := (Submodule.ne_bot_iff U).1 hUne
    have hli : LinearIndependent ℂ ![ψ, Θ ψ] :=
      linearIndependent_pair_of_inner_eq_zero hψ0 (Θ.map_ne_zero hψ0)
        (Θ.inner_self_time_reverse ψ)
    set S : Submodule ℂ V := Submodule.span ℂ (Set.range ![ψ, Θ ψ]) with hS
    have hSrank : Module.finrank ℂ S = 2 := by
      rw [hS, finrank_span_eq_card hli]
      simp
    have hmemψ : ψ ∈ S := Submodule.subset_span ⟨0, rfl⟩
    have hmemΘψ : Θ ψ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    have hSU : S ≤ U := by
      rw [hS, Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hψU
      · exact hinv _ hψU
    have hSinv : ∀ x ∈ S, Θ x ∈ S := by
      refine Θ.span_invariant ?_
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hmemΘψ
      · show Θ (Θ ψ) ∈ S
        rw [Θ.sq_eq_neg]
        exact Submodule.neg_mem _ hmemψ
    have hinv' : ∀ x ∈ Sᗮ ⊓ U, Θ x ∈ Sᗮ ⊓ U := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨Θ.orthogonal_invariant hSinv x hx1, hinv x hx2⟩
    have hsum : Module.finrank ℂ S + Module.finrank ℂ (Sᗮ ⊓ U : Submodule ℂ V)
        = Module.finrank ℂ U := Submodule.finrank_add_inf_finrank_orthogonal hSU
    rw [hSrank, hUrank] at hsum
    have hlt : Module.finrank ℂ (Sᗮ ⊓ U : Submodule ℂ V) < n := by omega
    have := ih _ hlt (Sᗮ ⊓ U) rfl hinv'
    rcases this with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

end TimeReversal

/--
**Kramers degeneracy, strong form.**  In a finite-dimensional state space, for a
half-integer-spin system (`Θ² = -1`) with time-reversal-invariant Hamiltonian `H`,
every energy eigenspace has *even* dimension.  In particular no level is nondegenerate.
-/
