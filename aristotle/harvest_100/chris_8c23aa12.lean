import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/
noncomputable def cyclotronFrequency (q B m : ℝ) : ℝ := q * B / m

/-- The `n`-th Landau level energy `ℏ ω_c (n + 1/2)`. -/
noncomputable def landauEnergy (hbar omega : ℝ) (n : ℕ) : ℝ := hbar * omega * (n + 1 / 2)

/-- The Landau levels are equally spaced, with gap `ℏ ω_c`. -/
theorem landauEnergy_succ_sub (hbar omega : ℝ) (n : ℕ) :
    landauEnergy hbar omega (n + 1) - landauEnergy hbar omega n = hbar * omega := by
  simp only [landauEnergy, Nat.cast_add, Nat.cast_one]
  ring

/-- The zero-point energy of the lowest Landau level. -/
theorem landauEnergy_zero (hbar omega : ℝ) :
    landauEnergy hbar omega 0 = hbar * omega / 2 := by
  simp [landauEnergy]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The tower of states `(a†)ⁿ ψ₀` obtained from the lowest Landau state `ψ₀` by
applying the raising operator `b = a†` repeatedly. -/
noncomputable def ladderState (b : V →ₗ[ℂ] V) (psi0 : V) (n : ℕ) : V := (b ^ n) psi0

@[simp] theorem ladderState_zero (b : V →ₗ[ℂ] V) (psi0 : V) :
    ladderState b psi0 0 = psi0 := by simp [ladderState]

theorem ladderState_succ (b : V →ₗ[ℂ] V) (psi0 : V) (n : ℕ) :
    ladderState b psi0 (n + 1) = b (ladderState b psi0 n) := by
  simp [ladderState, pow_succ']

/-- The number operator `N = a† a` acts on the `n`-th ladder state with eigenvalue `n`. -/
theorem number_apply_ladderState {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x) {psi0 : V} (h0 : a psi0 = 0) (n : ℕ) :
    b (a (ladderState b psi0 n)) = (n : ℂ) • ladderState b psi0 n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      rw [ladderState_succ, hcomm, map_add, ih, map_smul]
      push_cast
      module

/-- The squared norm of the `n`-th ladder state is `n!` times that of the ground state. -/
theorem inner_ladderState_self {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    {psi0 : V} (h0 : a psi0 = 0) (n : ℕ) :
    ⟪ladderState b psi0 n, ladderState b psi0 n⟫_ℂ
      = (n ! : ℂ) * ⟪psi0, psi0⟫_ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have key : ⟪ladderState b psi0 (n + 1), ladderState b psi0 (n + 1)⟫_ℂ
          = ((n : ℂ) + 1) * ⟪ladderState b psi0 n, ladderState b psi0 n⟫_ℂ := by
        rw [ladderState_succ, hadj, hcomm, inner_add_right,
          number_apply_ladderState hcomm h0 n, inner_smul_right]
        ring
      rw [key, ih, Nat.factorial_succ]
      push_cast
      ring

/-- Each ladder state is a genuine (nonzero) state. -/
theorem ladderState_ne_zero {a b : V →ₗ[ℂ] V}
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    {psi0 : V} (hpsi0 : psi0 ≠ 0) (h0 : a psi0 = 0) (n : ℕ) :
    ladderState b psi0 n ≠ 0 := by
  intro hzero
  have h := inner_ladderState_self hcomm hadj h0 n
  rw [hzero] at h
  simp only [inner_zero_left] at h
  have hfac : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have : ⟪psi0, psi0⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h2
    · exact absurd h1 hfac
    · exact h2
  exact hpsi0 (inner_self_eq_zero.mp this)

/--
**Landau levels.**

A charged particle of charge `q` and mass `m` in a uniform magnetic field `B` has, after
separation of variables in the Landau gauge, a Hamiltonian of harmonic-oscillator form
`H = ℏ ω_c (a† a + 1/2)` with cyclotron frequency `ω_c = q B / m`, where the ladder
operators satisfy the canonical commutation relation `[a, a†] = 1` and `a†` is the adjoint
of `a`.

Given a nonzero lowest state `ψ₀` annihilated by `a`, the states `ψ_n = (a†)ⁿ ψ₀` are
nonzero eigenstates of `H` with the equally spaced Landau energies
`E_n = ℏ ω_c (n + 1/2)`.
-/
theorem landau_levels {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (q B m hbar : ℝ) (a b : V →ₗ[ℂ] V)
    (hcomm : ∀ x, a (b x) = b (a x) + x)
    (hadj : ∀ x y : V, ⟪b x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    (psi0 : V) (hpsi0 : psi0 ≠ 0) (h0 : a psi0 = 0)
    (H : V →ₗ[ℂ] V)
    (hH : ∀ x, H x = ((hbar * cyclotronFrequency q B m : ℝ) : ℂ) •
      (b (a x) + ((1 / 2 : ℂ)) • x)) :
    ∀ n : ℕ, ladderState b psi0 n ≠ 0 ∧
      H (ladderState b psi0 n)
        = ((landauEnergy hbar (cyclotronFrequency q B m) n : ℝ) : ℂ)
          • ladderState b psi0 n := by
  intro n
  refine ⟨ladderState_ne_zero hcomm hadj hpsi0 h0 n, ?_⟩
  rw [hH, number_apply_ladderState hcomm h0 n]
  rw [landauEnergy]
  push_cast
  module

/-- The Landau Hamiltonian in the concrete Bargmann–Fock model. -/
noncomputable def fockHamiltonian (hbar omega : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omega : ℝ) : ℂ) • (fockB ∘ₗ fockA + (1 / 2 : ℂ) • LinearMap.id)

/--
The Landau level theorem is not vacuous: in the explicit Bargmann–Fock model (where the
ladder operators are differentiation and multiplication by the variable, with the Bargmann
inner product) all hypotheses hold, and the states `(a†)ⁿ ψ₀` are nonzero eigenstates of
the Landau Hamiltonian with energies `ℏ ω_c (n + 1/2)`, `ω_c = q B / m`.
-/
theorem landau_levels_fock (q B m hbar : ℝ) :
    ∀ n : ℕ, ladderState fockB fockVacuum n ≠ 0 ∧
      fockHamiltonian hbar (cyclotronFrequency q B m) (ladderState fockB fockVacuum n)
        = ((landauEnergy hbar (cyclotronFrequency q B m) n : ℝ) : ℂ)
          • ladderState fockB fockVacuum n :=
  landau_levels q B m hbar fockA fockB fock_comm fock_adjoint fockVacuum fockVacuum_ne_zero
    fockA_vacuum (fockHamiltonian hbar (cyclotronFrequency q B m)) (by
      intro x
      simp [fockHamiltonian])

end Frontier

import Mathlib

/-!
# A concrete Bargmann–Fock model for the Landau ladder operators

This file constructs an explicit complex inner product space carrying operators `a`, `b`
satisfying `[a, b] = 1`, with `b` adjoint to `a`, together with a nonzero vacuum vector
annihilated by `a`. It witnesses that the hypotheses of the Landau level theorem in
`RequestProject.Main` are satisfiable, so that theorem is not vacuous.

The space is `ℕ →₀ ℂ`, the space of polynomial coefficient sequences, equipped with the
Bargmann inner product `⟪p, q⟫ = ∑ n, n! * conj (p n) * q n`; `b` is multiplication by the
variable `X` and `a` is differentiation `d/dX`.
-/

open scoped ComplexConjugate Nat

namespace Frontier

/-- The Bargmann inner product on coefficient sequences. -/
noncomputable def fockInner (p q : ℕ →₀ ℂ) : ℂ :=
  ∑ n ∈ p.support, (n ! : ℂ) * conj (p n) * q n

theorem fockInner_eq_sum {p q : ℕ →₀ ℂ} {s : Finset ℕ} (hs : p.support ⊆ s) :
    fockInner p q = ∑ n ∈ s, (n ! : ℂ) * conj (p n) * q n := by
  refine Finset.sum_subset hs ?_
  intro x _ hx
  simp [Finsupp.notMem_support_iff.mp hx]

theorem fockInner_self (p : ℕ →₀ ℂ) :
    fockInner p p = ((∑ n ∈ p.support, (n ! : ℝ) * Complex.normSq (p n) : ℝ) : ℂ) := by
  rw [fockInner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

theorem fockInner_conj_symm (p q : ℕ →₀ ℂ) : conj (fockInner q p) = fockInner p q := by
  rw [fockInner_eq_sum (q := p) (s := p.support ∪ q.support) Finset.subset_union_right,
    fockInner_eq_sum (q := q) (s := p.support ∪ q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [mul_comm, mul_left_comm]

theorem fockInner_add_left (p q r : ℕ →₀ ℂ) :
    fockInner (p + q) r = fockInner p r + fockInner q r := by
  rw [fockInner_eq_sum (q := r) Finsupp.support_add,
    fockInner_eq_sum (p := p) (q := r) Finset.subset_union_left,
    fockInner_eq_sum (p := q) (q := r) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Finsupp.add_apply]
  ring

theorem fockInner_add_right (p q r : ℕ →₀ ℂ) :
    fockInner p (q + r) = fockInner p q + fockInner p r := by
  simp only [fockInner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Finsupp.add_apply]
  ring

theorem fockInner_smul_left (p q : ℕ →₀ ℂ) (r : ℂ) :
    fockInner (r • p) q = conj r * fockInner p q := by
  rw [fockInner_eq_sum (p := r • p) (q := q) (s := p.support) Finsupp.support_smul,
    fockInner_eq_sum (p := p) (q := q) (s := p.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Finsupp.smul_apply]
  ring

@[simp] theorem fockInner_zero_left (q : ℕ →₀ ℂ) : fockInner 0 q = 0 := by simp [fockInner]

@[simp] theorem fockInner_zero_right (p : ℕ →₀ ℂ) : fockInner p 0 = 0 := by simp [fockInner]

theorem fockInner_definite (p : ℕ →₀ ℂ) (h : fockInner p p = 0) : p = 0 := by
  rw [fockInner_self] at h
  have hsum : (∑ n ∈ p.support, (n ! : ℝ) * Complex.normSq (p n)) = 0 := by exact_mod_cast h
  have hnonneg : ∀ n ∈ p.support, 0 ≤ (n ! : ℝ) * Complex.normSq (p n) := fun n _ =>
    mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  ext n
  by_cases hn : n ∈ p.support
  · have h2 := hzero n hn
    have hns : Complex.normSq (p n) = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (by positivity)
      · exact h3
    simpa using Complex.normSq_eq_zero.mp hns
  · simp [Finsupp.notMem_support_iff.mp hn]

theorem fockInner_single_single (m k : ℕ) (c d : ℂ) :
    fockInner (Finsupp.single m c) (Finsupp.single k d)
      = if m = k then (m ! : ℂ) * conj c * d else 0 := by
  rw [fockInner_eq_sum (s := {m}) Finsupp.support_single_subset]
  simp only [Finset.sum_singleton, Finsupp.single_apply]
  by_cases h : m = k <;> simp [h, eq_comm]

noncomputable instance : Inner ℂ (ℕ →₀ ℂ) := ⟨fockInner⟩

/-- The Bargmann inner product makes `ℕ →₀ ℂ` an inner product space. -/
noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner := fockInner
  conj_inner_symm p q := fockInner_conj_symm p q
  re_inner_nonneg p := by
    show 0 ≤ (fockInner p p).re
    rw [fockInner_self, Complex.ofReal_re]
    exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  add_left p q r := fockInner_add_left p q r
  smul_left p q r := fockInner_smul_left p q r
  definite p h := fockInner_definite p h

noncomputable instance : NormedAddCommGroup (ℕ →₀ ℂ) := fockCore.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ (ℕ →₀ ℂ) := InnerProductSpace.ofCore fockCore.toCore

theorem fock_inner_def (p q : ℕ →₀ ℂ) : (inner ℂ p q : ℂ) = fockInner p q := rfl

/-- The annihilation operator: differentiation, `X ^ n ↦ n X ^ (n - 1)`. -/
noncomputable def fockA : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => (n : ℂ) • (Finsupp.lsingle (n - 1) : ℂ →ₗ[ℂ] (ℕ →₀ ℂ))

/-- The creation operator: multiplication by the variable, `X ^ n ↦ X ^ (n + 1)`. -/
noncomputable def fockB : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => (Finsupp.lsingle (n + 1) : ℂ →ₗ[ℂ] (ℕ →₀ ℂ))

@[simp] theorem fockA_single (n : ℕ) (c : ℂ) :
    fockA (Finsupp.single n c) = Finsupp.single (n - 1) ((n : ℂ) * c) := by
  simp [fockA, Finsupp.lsum_single, Finsupp.smul_single]

@[simp] theorem fockB_single (n : ℕ) (c : ℂ) :
    fockB (Finsupp.single n c) = Finsupp.single (n + 1) c := by
  simp [fockB, Finsupp.lsum_single]

/-- The canonical commutation relation `[a, b] = 1`. -/
theorem fock_comm (x : ℕ →₀ ℂ) : fockA (fockB x) = fockB (fockA x) + x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]; abel
  | single n c =>
      cases n with
      | zero => simp
      | succ k =>
          simp only [fockB_single, fockA_single, Nat.add_sub_cancel, ← Finsupp.single_add]
          congr 1
          push_cast
          ring

/-- The creation operator is adjoint to the annihilation operator. -/
theorem fock_adjoint (x y : ℕ →₀ ℂ) :
    (inner ℂ (fockB x) y : ℂ) = inner ℂ x (fockA y) := by
  simp only [fock_inner_def]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, fockInner_add_left, hp, hq, ← fockInner_add_left]
  | single m c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
          rw [fockInner_add_right, hp, hq, map_add, fockInner_add_right]
      | single k d =>
          rw [fockB_single, fockA_single, fockInner_single_single, fockInner_single_single]
          cases k with
          | zero => simp
          | succ j =>
              simp only [Nat.add_sub_cancel]
              by_cases h : m = j
              · subst h
                simp only [Nat.factorial_succ]
                push_cast
                ring
              · simp [h]

/-- The vacuum (lowest Landau level) state. -/
noncomputable def fockVacuum : ℕ →₀ ℂ := Finsupp.single 0 1

theorem fockVacuum_ne_zero : fockVacuum ≠ 0 := by
  simp [fockVacuum, Finsupp.single_eq_zero]

theorem fockA_vacuum : fockA fockVacuum = 0 := by
  simp [fockVacuum]

end Frontier

