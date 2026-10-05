/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

theorem number_eigenvalue_nat (A B : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} (hv : v ≠ 0) {μ : ℂ} (h : B (A v) = μ • v) :
    ∃ n : ℕ, μ = (n : ℂ) := by
  by_cases hex : ∃ n : ℕ, (A : V → V)^[n] v = 0
  · classical
    have hne0 : Nat.find hex ≠ 0 := by
      intro h0
      have hs := Nat.find_spec hex
      rw [h0] at hs
      exact hv (by simpa using hs)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne0
    have hw : (A : V → V)^[m] v ≠ 0 := Nat.find_min hex (by omega)
    have hzero : A ((A : V → V)^[m] v) = 0 := by
      have hs := Nat.find_spec hex
      rw [hm, Function.iterate_succ_apply' (f := (A : V → V))] at hs
      exact hs
    have hchain := number_ladder_iterate A B hcomm h m
    rw [hzero, map_zero] at hchain
    have hmu : μ - (m : ℂ) = 0 := by
      rcases smul_eq_zero.mp hchain.symm with h1 | h1
      · exact h1
      · exact absurd h1 hw
    exact ⟨m, by linear_combination hmu⟩
  · push_neg at hex
    have hbound : ∀ n : ℕ, (n : ℝ) ≤ μ.re := by
      intro n
      obtain ⟨r, hr0, hr⟩ :=
        number_eigenvalue_nonneg A B hadj (hex n) (number_ladder_iterate A B hcomm h n)
      have : μ.re - n = r := by
        have := congrArg Complex.re hr
        simpa using this
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt μ.re
    exact absurd (hbound n) (not_le.mpr hn)

/-- **Landau levels.**

A charged particle in a uniform magnetic field is described, after separating the cyclotron
degree of freedom, by the Hamiltonian `H = ℏ ω_c (a† a + 1/2)`, where the ladder operators
satisfy the canonical commutation relation `[a, a†] = 1` and `a†` is the adjoint of `a`.

This theorem says that any eigenvalue `E` of such a Hamiltonian (on a nonzero eigenvector)
is of the form `E = ℏ ω_c (n + 1/2)` for some natural number `n`: the Landau level spectrum. -/
