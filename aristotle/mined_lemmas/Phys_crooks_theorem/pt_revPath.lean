import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Statement: Crooks fluctuation theorem: P_F(W)/P_R(−W) = e^{β(W−ΔF)}.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real
open scoped Classical

namespace Phys

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- `pt x k` is the state of the trajectory `x` (of length `N + 1`) at time `k`. -/

lemma pt_revPath (x : Fin (N + 1) → S) {k : ℕ} (hk : k ≤ N) :
    pt (revPath x) k = pt x (N - k) := by
  have h1 : ((Fin.ofNat (N + 1) k : Fin (N + 1)) : ℕ) = k := by
    simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((Fin.ofNat (N + 1) (N - k) : Fin (N + 1)) : ℕ) = N - k := by
    simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h3 : Fin.rev (Fin.ofNat (N + 1) k) = Fin.ofNat (N + 1) (N - k) := by
    apply Fin.ext
    rw [Fin.val_rev, h1, h2]
    omega
  show x (Fin.rev (Fin.ofNat (N + 1) k)) = x (Fin.ofNat (N + 1) (N - k))
  rw [h3]

/-- A discrete-time driven Markov process: a protocol of Hamiltonians `E k` together with
transition kernels `K k` obeying detailed balance with respect to the Gibbs measure of `E (k+1)`
at inverse temperature `beta`. -/
structure Setup (S : Type*) [Fintype S] (N : ℕ) where
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  /-- the energy function at protocol step `k` -/
  E : ℕ → S → ℝ
  /-- the transition kernel used in the `k`-th relaxation step -/
  K : ℕ → S → S → ℝ
  K_pos : ∀ k x y, 0 < K k x y
  detailed_balance : ∀ k x y,
    Real.exp (-beta * E (k + 1) x) * K k x y = Real.exp (-beta * E (k + 1) y) * K k y x

namespace Setup

variable (P : Setup S N)

/-- Partition function of the Hamiltonian at protocol step `k`. -/
