import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The spectrum of the quantum harmonic oscillator, via ladder operators

We formalise the algebraic (ladder-operator) derivation of the spectrum of the quantum
harmonic oscillator.

The data is packaged in `QPhys.Ladder`: a complex inner product space `V` (the space of
"nice" states), an annihilation operator `a`, a creation operator `a†`, mutually adjoint,
satisfying the canonical commutation relation `[a, a†] = 1`, together with a nonzero
vacuum vector annihilated by `a`.

The number operator is `N = a† a` and the Hamiltonian is `H = ℏω (N + 1/2)`.

The main result `QPhys.oscillator_spectrum` says that the eigenvalues of `H` are exactly
the numbers `ℏω (n + 1/2)` for `n : ℕ`.
-/

namespace QPhys

/-- A pair of ladder operators on a complex inner product space, together with a vacuum
vector.  `ann` is the annihilation operator `a`, `cre` is the creation operator `a†`;
they are adjoint to each other and satisfy the canonical commutation relation
`[a, a†] = 1`.  The vector `vac` is a nonzero vacuum state, i.e. `a vac = 0`. -/
structure Ladder (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- the annihilation operator `a` -/
  ann : V →ₗ[ℂ] V
  /-- the creation operator `a†` -/
  cre : V →ₗ[ℂ] V
  /-- `cre` is the adjoint of `ann` -/
  adj : ∀ x y : V, inner ℂ (ann x) y = inner ℂ x (cre y)
  /-- the canonical commutation relation `[a, a†] = 1` -/
  comm : ∀ x : V, ann (cre x) - cre (ann x) = x
  /-- the vacuum state -/
  vac : V
  /-- the vacuum state is nonzero -/
  vac_ne_zero : vac ≠ 0
  /-- the vacuum state is annihilated by `a` -/
  ann_vac : ann vac = 0

namespace Ladder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (L : Ladder V)

/-- The number operator `N = a† a`. -/
def number : V →ₗ[ℂ] V := L.cre ∘ₗ L.ann

/-- The Hamiltonian `H = ℏ ω (N + 1/2)` of the harmonic oscillator. -/
noncomputable def hamiltonian (hbar omega : ℝ) : V →ₗ[ℂ] V :=
  (((hbar * omega : ℝ) : ℂ)) • (L.number + (1 / 2 : ℂ) • LinearMap.id)

end Ladder

/-- `μ` is an eigenvalue of `f` iff there is a nonzero `x` with `f x = μ • x`. -/
theorem hasEigenvalue_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (μ : ℂ) :
    f.HasEigenvalue μ ↔ ∃ x ≠ 0, f x = μ • x := by
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := h.exists_hasEigenvector
    exact ⟨x, hx0, Module.End.mem_eigenspace_iff.1 hx⟩
  · rintro ⟨x, hx0, hx⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩

namespace Ladder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (L : Ladder V)

/-- The adjoint relation, read in the other direction. -/
theorem adj' (x y : V) : inner ℂ (L.cre x) y = inner ℂ x (L.ann y) := by
  rw [← inner_conj_symm (𝕜 := ℂ) (L.cre x) y, ← L.adj y x, inner_conj_symm]

theorem number_apply (x : V) : L.number x = L.cre (L.ann x) := rfl

/-- The commutation relation, rewritten as `a a† = N + 1`. -/
theorem ann_cre_apply (x : V) : L.ann (L.cre x) = L.number x + x := by
  have h := L.comm x
  rw [L.number_apply]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- `⟪x, N x⟫ = ⟪a x, a x⟫`. -/
theorem inner_number_self (x : V) :
    inner ℂ x (L.number x) = inner ℂ (L.ann x) (L.ann x) := (L.adj x (L.ann x)).symm

/-- Eigenvalues of the number operator have nonnegative real part. -/
theorem number_eigen_re_nonneg {μ : ℂ} {x : V} (hx : x ≠ 0) (h : L.number x = μ • x) :
    0 ≤ μ.re := by
  have hxx : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have haa : inner ℂ (L.ann x) (L.ann x) = ((‖L.ann x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have key : μ * ((‖x‖ ^ 2 : ℝ) : ℂ) = ((‖L.ann x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hxx, ← haa, ← inner_smul_right, ← h]
    exact L.inner_number_self x
  have hre := congrArg Complex.re key
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h2 : 0 ≤ μ.re * ‖x‖ ^ 2 := by rw [hre]; positivity
  have h3 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos hpos 2
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_neg_of_pos hneg h3
  linarith

/-- Applying `a` lowers the eigenvalue by one. -/
theorem number_ann_eigen {μ : ℂ} {x : V} (h : L.number x = μ • x) :
    L.number (L.ann x) = (μ - 1) • L.ann x := by
  have h2 : L.ann (L.cre (L.ann x)) = L.number (L.ann x) + L.ann x := L.ann_cre_apply (L.ann x)
  have h3 : L.ann (L.number x) = μ • L.ann x := by rw [h, map_smul]
  rw [L.number_apply x] at h3
  rw [h2] at h3
  rw [sub_smul, one_smul, ← h3]
  abel

/-- Applying `a†` raises the eigenvalue by one. -/
theorem number_cre_eigen {μ : ℂ} {x : V} (h : L.number x = μ • x) :
    L.number (L.cre x) = (μ + 1) • L.cre x := by
  have h2 : L.ann (L.cre x) = (μ + 1) • x := by
    rw [L.ann_cre_apply, h, add_smul, one_smul]
  rw [L.number_apply, h2, map_smul]

/-- If `x` is an eigenvector of `N` with nonzero eigenvalue then `a x ≠ 0`. -/
theorem ann_ne_zero {μ : ℂ} {x : V} (hx : x ≠ 0) (h : L.number x = μ • x) (hμ : μ ≠ 0) :
    L.ann x ≠ 0 := by
  intro hax
  rw [L.number_apply, hax, map_zero] at h
  rcases smul_eq_zero.1 h.symm with h' | h'
  · exact hμ h'
  · exact hx h'

/-- `⟪a† x, a† x⟫ = (μ + 1) ⟪x, x⟫` for an eigenvector `x` of `N` with eigenvalue `μ`. -/
theorem inner_cre_cre {μ : ℂ} {x : V} (h : L.number x = μ • x) :
    inner ℂ (L.cre x) (L.cre x) = (μ + 1) * inner ℂ x x := by
  have h2 : L.ann (L.cre x) = (μ + 1) • x := by
    rw [L.ann_cre_apply, h, add_smul, one_smul]
  rw [L.adj', h2, inner_smul_right]

/-- Raising a nonzero eigenvector with a natural eigenvalue gives a nonzero vector. -/
theorem cre_ne_zero {n : ℕ} {x : V} (hx : x ≠ 0) (h : L.number x = (n : ℂ) • x) :
    L.cre x ≠ 0 := by
  intro hcx
  have h1 := L.inner_cre_cre h
  rw [hcx, inner_zero_left] at h1
  have hxx : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hxx] at h1
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hx' : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    exact_mod_cast hpos.ne'
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, Ne, Nat.cast_eq_zero]
    omega
  rcases mul_eq_zero.1 h1.symm with h' | h'
  · exact hn h'
  · exact hx' h'

/-- Downward induction along the ladder: every eigenvalue of `N` with real part `< n`
is a natural number. -/
theorem number_eigenvalue_nat_aux (n : ℕ) :
    ∀ (μ : ℂ) (x : V), x ≠ 0 → L.number x = μ • x → μ.re < n → ∃ k : ℕ, μ = (k : ℂ) := by
  induction n with
  | zero =>
      intro μ x hx h hlt
      have := L.number_eigen_re_nonneg hx h
      simp only [Nat.cast_zero] at hlt
      linarith
  | succ n ih =>
      intro μ x hx h hlt
      by_cases hμ : μ = 0
      · exact ⟨0, by simp [hμ]⟩
      · have hax : L.ann x ≠ 0 := L.ann_ne_zero hx h hμ
        have h2 : L.number (L.ann x) = (μ - 1) • L.ann x := L.number_ann_eigen h
        have h3 : (μ - 1).re < n := by
          have : (μ - 1).re = μ.re - 1 := by simp
          rw [this]
          have : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
          rw [this] at hlt
          linarith
        obtain ⟨k, hk⟩ := ih (μ - 1) (L.ann x) hax h2 h3
        exact ⟨k + 1, by push_cast; linear_combination hk⟩

/-- Every eigenvalue of the number operator is a natural number. -/
theorem number_eigenvalue_nat {μ : ℂ} (h : Module.End.HasEigenvalue L.number μ) :
    ∃ k : ℕ, μ = (k : ℂ) := by
  obtain ⟨x, hx, hxe⟩ := (hasEigenvalue_iff L.number μ).1 h
  obtain ⟨n, hn⟩ := exists_nat_gt μ.re
  exact L.number_eigenvalue_nat_aux n μ x hx hxe hn

/-- The `n`-th excited state `(a†)ⁿ vac` is a nonzero eigenvector of `N` with
eigenvalue `n`. -/
theorem cre_pow_vac (n : ℕ) :
    (L.cre ^ n) L.vac ≠ 0 ∧ L.number ((L.cre ^ n) L.vac) = (n : ℂ) • (L.cre ^ n) L.vac := by
  induction n with
  | zero =>
      refine ⟨by simpa using L.vac_ne_zero, ?_⟩
      have h0 : (L.cre ^ 0) L.vac = L.vac := by simp
      rw [h0, Nat.cast_zero, zero_smul, L.number_apply, L.ann_vac, map_zero]
  | succ n ih =>
      obtain ⟨hne, heig⟩ := ih
      have hstep : (L.cre ^ (n + 1)) L.vac = L.cre ((L.cre ^ n) L.vac) := by
        rw [pow_succ']
        rfl
      refine ⟨?_, ?_⟩
      · rw [hstep]
        exact L.cre_ne_zero hne heig
      · rw [hstep, L.number_cre_eigen heig]
        push_cast
        ring_nf

/-- Every natural number is an eigenvalue of the number operator. -/
theorem number_hasEigenvalue_nat (n : ℕ) : Module.End.HasEigenvalue L.number (n : ℂ) := by
  obtain ⟨hne, heig⟩ := L.cre_pow_vac n
  exact (hasEigenvalue_iff L.number (n : ℂ)).2 ⟨_, hne, heig⟩

/-- The eigenvalues of the number operator are exactly the natural numbers. -/
theorem number_spectrum (μ : ℂ) :
    Module.End.HasEigenvalue L.number μ ↔ ∃ n : ℕ, μ = (n : ℂ) := by
  constructor
  · exact L.number_eigenvalue_nat
  · rintro ⟨n, rfl⟩
    exact L.number_hasEigenvalue_nat n

theorem hamiltonian_apply (hbar omega : ℝ) (x : V) :
    L.hamiltonian hbar omega x
      = ((hbar * omega : ℝ) : ℂ) • L.number x + (((hbar * omega : ℝ) : ℂ) / 2) • x := by
  simp only [hamiltonian, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq,
    smul_add, smul_smul]
  congr 2
  ring

/-- The eigenvector equation for `H` in terms of `N`. -/
theorem hamiltonian_eq_iff {hbar omega : ℝ} (hc : ((hbar * omega : ℝ) : ℂ) ≠ 0) (μ : ℂ)
    (x : V) :
    L.hamiltonian hbar omega x = μ • x ↔
      L.number x = (μ / ((hbar * omega : ℝ) : ℂ) - 1 / 2) • x := by
  rw [L.hamiltonian_apply]
  set c : ℂ := ((hbar * omega : ℝ) : ℂ) with hcdef
  clear_value c
  constructor
  · intro h
    have h2 : c • L.number x = (μ - c / 2) • x := by
      rw [sub_smul, ← h]
      abel
    calc L.number x = c⁻¹ • (c • L.number x) := by
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • ((μ - c / 2) • x) := by rw [h2]
      _ = (μ / c - 1 / 2) • x := by
            rw [smul_smul]
            congr 1
            field_simp
  · intro h
    rw [h, smul_smul, ← add_smul]
    congr 1
    field_simp
    ring

/-- Eigenvalues of `H` correspond to eigenvalues of `N`. -/
theorem hamiltonian_hasEigenvalue_iff {hbar omega : ℝ}
    (hc : ((hbar * omega : ℝ) : ℂ) ≠ 0) (μ : ℂ) :
    Module.End.HasEigenvalue (L.hamiltonian hbar omega) μ ↔
      Module.End.HasEigenvalue L.number (μ / ((hbar * omega : ℝ) : ℂ) - 1 / 2) := by
  rw [hasEigenvalue_iff, hasEigenvalue_iff]
  constructor
  · rintro ⟨x, hx, hxe⟩
    exact ⟨x, hx, (L.hamiltonian_eq_iff hc μ x).1 hxe⟩
  · rintro ⟨x, hx, hxe⟩
    exact ⟨x, hx, (L.hamiltonian_eq_iff hc μ x).2 hxe⟩

end Ladder

/-- **Spectrum of the quantum harmonic oscillator.**
For a system of ladder operators `a`, `a†` on a complex inner product space, with
`[a, a†] = 1`, `a†` the adjoint of `a`, and a nonzero vacuum vector killed by `a`, the
eigenvalues of the Hamiltonian `H = ℏω (a†a + 1/2)` are exactly the numbers
`ℏω (n + 1/2)`, `n : ℕ`. -/
theorem oscillator_spectrum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (L : Ladder V) {hbar omega : ℝ} (hhbar : 0 < hbar) (homega : 0 < omega) (μ : ℂ) :
    Module.End.HasEigenvalue (L.hamiltonian hbar omega) μ ↔
      ∃ n : ℕ, μ = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) := by
  have hcr : hbar * omega ≠ 0 := by positivity
  have hc : ((hbar * omega : ℝ) : ℂ) ≠ 0 := by
    simpa using hcr
  rw [L.hamiltonian_hasEigenvalue_iff hc μ, L.number_spectrum]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp at hn
    linear_combination hn / 2
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    field_simp
    ring

end QPhys

import RequestProject.Main

set_option maxHeartbeats 1000000

/-!
# A concrete model of the ladder operators: the polynomial Fock space

To show that the hypotheses of `QPhys.oscillator_spectrum` are not vacuous, we exhibit a
concrete system of ladder operators: the space `ℂ[X]` of complex polynomials, equipped
with the inner product

`⟪p, q⟫ = ∑ n, n! * conj (p.coeff n) * q.coeff n`,

with annihilation operator `a = d/dX`, creation operator `a† = (X * ·)` and vacuum the
constant polynomial `1`.  In the (non-normalised) basis `Xⁿ` we have
`a (Xⁿ) = n Xⁿ⁻¹`, `a† (Xⁿ) = Xⁿ⁺¹`, and `⟪Xᵐ, Xⁿ⟫ = n! δₘₙ`.
-/

namespace QPhys.Fock

open Polynomial Finset ComplexConjugate

/-! ### Purely algebraic facts about `d/dX` and `X * ·` -/

/-- The canonical commutation relation `[d/dX, X·] = 1` for polynomials. -/
theorem derivative_X_mul_sub (p : Polynomial ℂ) :
    derivative (X * p) - X * derivative p = p := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_X]
  ring

theorem derivative_one_eq_zero : derivative (1 : Polynomial ℂ) = 0 :=
  Polynomial.derivative_one

/-- `X * q` has support inside the shift of the support of `q`. -/
theorem support_X_mul_subset (q : Polynomial ℂ) :
    (X * q).support ⊆ q.support.image (· + 1) := by
  intro m hm
  have hm' : (X * q).coeff m ≠ 0 := Polynomial.mem_support_iff.1 hm
  match m with
  | 0 =>
      refine absurd ?_ hm'
      simp
  | (k + 1) =>
      rw [Polynomial.coeff_X_mul] at hm'
      exact Finset.mem_image.2 ⟨k, Polynomial.mem_support_iff.2 hm', rfl⟩

/-! ### The Fock inner product -/

/-- The Fock inner product on complex polynomials:
`⟪p, q⟫ = ∑ n, n! * conj (p.coeff n) * q.coeff n`. -/
noncomputable def pinner (p q : Polynomial ℂ) : ℂ :=
  ∑ n ∈ q.support, (n.factorial : ℂ) * conj (p.coeff n) * q.coeff n

theorem pinner_eq_sum (p q : Polynomial ℂ) {s : Finset ℕ} (hs : q.support ⊆ s) :
    pinner p q = ∑ n ∈ s, (n.factorial : ℂ) * conj (p.coeff n) * q.coeff n := by
  apply Finset.sum_subset hs
  intro n _ hn
  rw [Polynomial.notMem_support_iff.1 hn]
  ring

theorem pinner_add_left (p₁ p₂ q : Polynomial ℂ) :
    pinner (p₁ + p₂) q = pinner p₁ q + pinner p₂ q := by
  unfold pinner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.coeff_add, map_add]
  ring

theorem pinner_smul_left (r : ℂ) (p q : Polynomial ℂ) :
    pinner (r • p) q = conj r * pinner p q := by
  unfold pinner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

theorem pinner_conj_symm (p q : Polynomial ℂ) : conj (pinner q p) = pinner p q := by
  rw [pinner_eq_sum q p (s := p.support ∪ q.support) Finset.subset_union_left,
    pinner_eq_sum p q (s := p.support ∪ q.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_conj, Complex.conj_natCast]
  ring

theorem pinner_self (p : Polynomial ℂ) :
    pinner p p
      = ((∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n) : ℝ) : ℂ) := by
  unfold pinner
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]

theorem pinner_self_term_nonneg (p : Polynomial ℂ) (n : ℕ) :
    0 ≤ (n.factorial : ℝ) * Complex.normSq (p.coeff n) :=
  mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem pinner_self_nonneg (p : Polynomial ℂ) : 0 ≤ (pinner p p).re := by
  rw [pinner_self]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun n _ => pinner_self_term_nonneg p n

theorem pinner_definite (p : Polynomial ℂ) (h : pinner p p = 0) : p = 0 := by
  rw [pinner_self] at h
  have h' : (∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n)) = 0 := by
    exact_mod_cast congrArg Complex.re h
  have hterm : ∀ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n) = 0 :=
    fun n hn => (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => pinner_self_term_nonneg p i)).1 h' n hn
  ext n
  by_cases hn : n ∈ p.support
  · have hz := hterm n hn
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hns : Complex.normSq (p.coeff n) = 0 := by
      rcases mul_eq_zero.1 hz with h1 | h1
      · exact absurd h1 hfac.ne'
      · exact h1
    simpa using Complex.normSq_eq_zero.1 hns
  · simpa using Polynomial.notMem_support_iff.1 hn

/-- The creation operator `a† = (X * ·)` is the adjoint of the annihilation operator
`a = d/dX`. -/
theorem pinner_derivative_left (p q : Polynomial ℂ) :
    pinner (derivative p) q = pinner p (X * q) := by
  rw [pinner_eq_sum p (X * q) (support_X_mul_subset q),
    Finset.sum_image (by intro a _ b _ h; simpa using h)]
  unfold pinner
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.coeff_derivative, Polynomial.coeff_X_mul]
  have hfac : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  simp only [map_mul, map_add, Complex.conj_natCast, map_one]
  ring

/-! ### The inner product space structure and the ladder operators -/

/-- The Fock inner product as an `InnerProductSpace.Core` structure on `ℂ[X]`. -/
noncomputable def polyCore : InnerProductSpace.Core ℂ (Polynomial ℂ) where
  inner := pinner
  conj_inner_symm := pinner_conj_symm
  re_inner_nonneg := pinner_self_nonneg
  add_left := pinner_add_left
  smul_left := fun x y r => pinner_smul_left r x y
  definite := pinner_definite

noncomputable instance : NormedAddCommGroup (Polynomial ℂ) :=
  polyCore.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ (Polynomial ℂ) :=
  InnerProductSpace.ofCore polyCore.toCore

theorem inner_eq_pinner (p q : Polynomial ℂ) : inner ℂ p q = pinner p q := rfl

/-- The polynomial Fock model of the ladder operators: `a = d/dX`, `a† = (X * ·)`,
vacuum `1`. -/
noncomputable def polyLadder : QPhys.Ladder (Polynomial ℂ) where
  ann := Polynomial.derivative
  cre := LinearMap.mulLeft ℂ (X : Polynomial ℂ)
  adj := fun p q => by
    rw [inner_eq_pinner, inner_eq_pinner]
    exact pinner_derivative_left p q
  comm := fun p => by
    simp only [LinearMap.mulLeft_apply]
    exact derivative_X_mul_sub p
  vac := 1
  vac_ne_zero := one_ne_zero
  ann_vac := derivative_one_eq_zero

end QPhys.Fock

namespace QPhys

/-- The hypotheses of `QPhys.oscillator_spectrum` are satisfiable: there is a genuine
system of ladder operators, namely the polynomial Fock space. -/
theorem exists_ladder :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V), Nonempty (Ladder V) :=
  ⟨Polynomial ℂ, inferInstance, inferInstance, ⟨QPhys.Fock.polyLadder⟩⟩

/-- The spectrum of the harmonic oscillator Hamiltonian in the concrete polynomial Fock
model: the eigenvalues of `H = ℏω (a†a + 1/2)` are exactly `ℏω (n + 1/2)`, `n : ℕ`. -/
theorem oscillator_spectrum_poly {hbar omega : ℝ} (hhbar : 0 < hbar) (homega : 0 < omega)
    (μ : ℂ) :
    Module.End.HasEigenvalue (QPhys.Fock.polyLadder.hamiltonian hbar omega) μ ↔
      ∃ n : ℕ, μ = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) :=
  oscillator_spectrum QPhys.Fock.polyLadder hhbar homega μ

end QPhys

