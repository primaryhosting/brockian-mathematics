/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module doc comments,
-- so the header above is written as a plain block comment and repeated below.)
import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-!
## The algebraic core of the Lieb–Schultz–Mattis argument

If a Hamiltonian commutes with two symmetries that *anticommute* with each other, then
every energy level is (at least) two-fold degenerate.  This is the finite-volume mechanism
behind the Lieb–Schultz–Mattis theorem: on a half-integer-spin chain of odd length the two
π-rotations about the `x`- and `z`-axes anticommute, so no energy level — in particular no
ground level — can be a simple eigenvalue.
-/

/-- **Degeneracy from anticommuting symmetries.**
Let `A` be an operator on a finite-dimensional complex vector space, and let `S`, `K` be two
operators commuting with `A` such that `S` is an involution, `K` is injective and `S`, `K`
anticommute.  Then every eigenvalue of `A` has an eigenspace of dimension at least `2`. -/

theorem degenerate_of_anticommuting_symmetries
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (A S K : V →ₗ[ℂ] V)
    (hS : S ∘ₗ S = LinearMap.id)
    (hK : Function.Injective K)
    (hAS : A ∘ₗ S = S ∘ₗ A) (hAK : A ∘ₗ K = K ∘ₗ A)
    (hSK : S ∘ₗ K = -(K ∘ₗ S))
    {E : ℂ} {v : V} (hv : v ≠ 0) (hAv : A v = E • v) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace A E) := by
  set W : Submodule ℂ V := Module.End.eigenspace A E with hW
  have memW : ∀ x : V, x ∈ W ↔ A x = E • x := by
    intro x; rw [hW, Module.End.mem_eigenspace_iff]
  -- `S` and `K` preserve the eigenspace
  have hSmem : ∀ x : V, x ∈ W → S x ∈ W := by
    intro x hx
    rw [memW] at hx ⊢
    have : (A ∘ₗ S) x = (S ∘ₗ A) x := by rw [hAS]
    simpa [hx, map_smul] using this
  have hKmem : ∀ x : V, x ∈ W → K x ∈ W := by
    intro x hx
    rw [memW] at hx ⊢
    have : (A ∘ₗ K) x = (K ∘ₗ A) x := by rw [hAK]
    simpa [hx, map_smul] using this
  have hSS : ∀ x : V, S (S x) = x := by
    intro x
    have : (S ∘ₗ S) x = LinearMap.id (R := ℂ) x := by rw [hS]
    simpa using this
  have hanti : ∀ x : V, S (K x) = -K (S x) := by
    intro x
    have : (S ∘ₗ K) x = (-(K ∘ₗ S)) x := by rw [hSK]
    simpa using this
  -- an eigenvector of the involution `S` inside the eigenspace, with eigenvalue `±1`
  obtain ⟨w, hwW, hw0, ε, hε0, hSw⟩ :
      ∃ w : V, w ∈ W ∧ w ≠ 0 ∧ ∃ ε : ℂ, ε ≠ 0 ∧ S w = ε • w := by
    by_cases h : v + S v = 0
    · refine ⟨v, (memW v).2 hAv, hv, -1, by norm_num, ?_⟩
      have : S v = -v := by
        have := h
        linear_combination (norm := module) this
      rw [this]; module
    · refine ⟨v + S v, W.add_mem ((memW v).2 hAv) (hSmem v ((memW v).2 hAv)), h, 1,
        one_ne_zero, ?_⟩
      rw [map_add, hSS]
      module
  have hKw0 : K w ≠ 0 := fun h => hw0 (hK (by simpa using h))
  have hKwW : K w ∈ W := hKmem w hwW
  -- `w` and `K w` are linearly independent
  have hli : LinearIndependent ℂ ![(⟨w, hwW⟩ : W), ⟨K w, hKwW⟩] := by
    apply LinearIndependent.of_comp W.subtype
    have hcomp : (⇑W.subtype) ∘ ![(⟨w, hwW⟩ : W), ⟨K w, hKwW⟩] = ![w, K w] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp, LinearIndependent.pair_iff]
    intro a b hab
    have hSapp : a • (ε • w) + b • (-(ε • K w)) = 0 := by
      have := congrArg S hab
      rw [map_add, map_smul, map_smul, map_zero, hSw, hanti w, hSw] at this
      simpa [smul_smul] using this
    have h1 : ε • (a • w - b • K w) = 0 := by
      linear_combination (norm := module) hSapp
    have h2 : a • w - b • K w = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact absurd h hε0
      · exact h
    have ha : (2 : ℂ) • (a • w) = 0 := by
      linear_combination (norm := module) hab + h2
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 ha with h | h
      · norm_num at h
      · rcases smul_eq_zero.1 h with h | h
        · exact h
        · exact absurd h hw0
    refine ⟨ha0, ?_⟩
    have : b • K w = 0 := by
      rw [ha0] at hab
      simpa using hab
    rcases smul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hKw0
  have := hli.fintype_card_le_finrank
  simpa using this

/-!
## A concrete half-integer-spin (spin-1/2) chain
-/

/-- The Hilbert space of a chain of `L` spin-1/2 sites: functions on the classical
configurations `Fin L → Bool` (each site carries a two-dimensional, i.e. spin-1/2, space). -/
abbrev Chain (L : ℕ) := (Fin L → Bool) → ℂ

/-- The number of up-spins of a configuration. -/
