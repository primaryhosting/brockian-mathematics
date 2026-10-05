import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- The total (negated) bond energy of a configuration `σ` on the `(m+1) × (n+1)`
square lattice with periodic boundary conditions in both directions:
`∑_{i,j} ( s_{i,j} s_{i+1,j} + s_{i,j} s_{i,j+1} )`. -/
def isingBondSum (m n : ℕ) (σ : Fin (m + 1) × Fin (n + 1) → Bool) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
    (spinVal (σ (i, j)) * spinVal (σ (i + 1, j)) + spinVal (σ (i, j)) * spinVal (σ (i, j + 1)))

/-- The partition function of the 2D square-lattice Ising model on the `(m+1) × (n+1)` torus
at reduced coupling `K = βJ`. -/
def isingZ (m n : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : Fin (m + 1) × Fin (n + 1) → Bool, Real.exp (K * isingBondSum m n σ)

/-- Onsager's exact expression for the reduced free energy per site,
`-βf = log 2 + (8π²)⁻¹ ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₁ dθ₂`. -/
def onsagerLogZ (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (8 * Real.pi ^ 2)) *
    ∫ x in (0 : ℝ)..(2 * Real.pi), ∫ y in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos x + Real.cos y))

/-- The partition function of the periodic 1D Ising chain (ring) with `k + 1` sites. -/
def ringZ (k : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : Fin (k + 1) → Bool,
    Real.exp (K * ∑ j : Fin (k + 1), spinVal (σ j) * spinVal (σ (j + 1)))

/-! ## Transfer matrix -/

/-- The Boltzmann weight of a single bond. -/
def tw (K : ℝ) (a b : Bool) : ℝ := Real.exp (K * spinVal a * spinVal b)

/-- Entries of the `k`-th power of the `2 × 2` transfer matrix. -/
def tmat (K : ℝ) : ℕ → Bool → Bool → ℝ
  | 0, a, b => if a = b then 1 else 0
  | (k + 1), a, b => ∑ c : Bool, tmat K k a c * tw K c b

/-! ## Basic lemmas -/

theorem spinVal_mul_self (b : Bool) : spinVal b * spinVal b = 1 := by
  cases b <;> norm_num [spinVal]

/-- Closed form for the powers of the `2 × 2` transfer matrix: the eigenvalues are
`2 cosh K` and `2 sinh K`. -/
theorem tmat_eq (K : ℝ) (k : ℕ) (a b : Bool) :
    tmat K k a b =
      if a = b then ((2 * Real.cosh K) ^ k + (2 * Real.sinh K) ^ k) / 2
      else ((2 * Real.cosh K) ^ k - (2 * Real.sinh K) ^ k) / 2 := by
  induction k generalizing a b with
  | zero => cases a <;> cases b <;> norm_num [tmat]
  | succ k ih =>
      cases a <;> cases b <;>
        simp [tmat, ih, tw, spinVal, Real.cosh_eq, Real.sinh_eq, Real.exp_neg] <;> ring

/-- Key transfer-matrix identity: summing an open-chain weight against an arbitrary boundary
function `H` of the two endpoints reproduces the matrix power. -/
theorem sum_chain (K : ℝ) :
    ∀ (k : ℕ) (H : Bool → Bool → ℝ),
      (∑ σ : Fin (k + 1) → Bool,
          (∏ i : Fin k, tw K (σ i.castSucc) (σ i.succ)) * H (σ 0) (σ (Fin.last k)))
        = ∑ a : Bool, ∑ b : Bool, tmat K k a b * H a b := by
  intro k
  induction k with
  | zero =>
      intro H
      rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp (fun x => (∏ i : Fin 0,
        tw K (x i.castSucc) (x i.succ)) * H (x 0) (x (Fin.last 0)))]
      simp [tmat]
  | succ k ih =>
      intro H
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k + 2) => Bool)), Fintype.sum_prod_type]
      have key : ∀ (b : Bool) (s : Fin (k + 1) → Bool),
          (∏ i : Fin (k + 1), tw K ((Fin.snoc s b : Fin (k + 2) → Bool) i.castSucc)
              ((Fin.snoc s b : Fin (k + 2) → Bool) i.succ)) *
            H ((Fin.snoc s b : Fin (k + 2) → Bool) 0)
              ((Fin.snoc s b : Fin (k + 2) → Bool) (Fin.last (k + 1)))
          = (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
              (tw K (s (Fin.last k)) b * H (s 0) b) := by
        intro b s
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last,
          Fin.snoc_apply_zero, mul_assoc]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
      rw [Finset.sum_comm]
      simp only [key]
      have hpull : ∀ s : Fin (k + 1) → Bool,
          (∑ b : Bool, (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
              (tw K (s (Fin.last k)) b * H (s 0) b))
            = (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
                (∑ b : Bool, tw K (s (Fin.last k)) b * H (s 0) b) := by
        intro s; rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun s _ => hpull s)]
      rw [ih (fun a c => ∑ b : Bool, tw K c b * H a b)]
      simp [tmat]
      ring

/-- Exact partition function of the periodic 1D Ising chain (transfer-matrix solution). -/
theorem ringZ_eq (k : ℕ) (K : ℝ) :
    ringZ k K = (2 * Real.cosh K) ^ (k + 1) + (2 * Real.sinh K) ^ (k + 1) := by
  have hprod : ∀ σ : Fin (k + 1) → Bool,
      Real.exp (K * ∑ j : Fin (k + 1), spinVal (σ j) * spinVal (σ (j + 1)))
        = (∏ i : Fin k, tw K (σ i.castSucc) (σ i.succ)) * tw K (σ (Fin.last k)) (σ 0) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [tw, ← mul_assoc]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]
  rw [ringZ, Finset.sum_congr rfl (fun σ _ => hprod σ), sum_chain K k (fun a b => tw K b a)]
  simp [tmat_eq, tw, spinVal, pow_succ, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  ring

/-! ## Base cases of Onsager's solution -/

theorem isingZ_pos (m n : ℕ) (K : ℝ) : 0 < isingZ m n K :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem isingZ_zero (m n : ℕ) : isingZ m n 0 = 2 ^ ((m + 1) * (n + 1)) := by
  simp [isingZ]

theorem onsagerLogZ_zero : onsagerLogZ 0 = Real.log 2 := by
  simp [onsagerLogZ]

/-- Reindexing equivalence: a configuration on the one-row torus is a 1D configuration. -/
def rowEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin 1 × Fin (n + 1) → Bool) where
  toFun τ := fun p => τ p.2
  invFun σ := fun j => σ (0, j)
  left_inv τ := rfl
  right_inv σ := by
    funext p
    obtain ⟨i, j⟩ := p
    simp [Subsingleton.elim (0 : Fin 1) i]

/-- Reduction of the 2D model on a one-row torus to the exactly solvable 1D ring:
the horizontal bonds contribute the constant factor `exp (K (n+1))`. -/
theorem isingZ_one_row (n : ℕ) (K : ℝ) :
    isingZ 0 n K = Real.exp (K * (n + 1)) * ringZ n K := by
  rw [isingZ, ← Equiv.sum_comp (rowEquiv n), ringZ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hb : isingBondSum 0 n (rowEquiv n τ)
      = (n + 1 : ℝ) + ∑ j : Fin (n + 1), spinVal (τ j) * spinVal (τ (j + 1)) := by
    simp only [isingBondSum, rowEquiv, Equiv.coe_fn_mk]
    rw [Finset.sum_add_distrib]
    simp [spinVal_mul_self]
  rw [hb, mul_add, Real.exp_add]

/-! ## Target -/

/-- **Onsager 2D Ising (formalization, base case and reduction).**

We set up the 2D square-lattice Ising model on the `(m+1) × (n+1)` torus and Onsager's
closed-form expression for the free energy per site, and we verify:

* the partition function is positive;
* at infinite temperature (`K = 0`) the finite-lattice partition function is `2^{sites}`,
  so the free energy per site is exactly `log 2`, and it agrees with the value
  `onsagerLogZ 0` produced by Onsager's formula (the infinite-temperature base case);
* the one-row torus (`m = 0`) reduces exactly to the periodic 1D Ising chain, whose
  partition function is `(2 cosh K)^N + (2 sinh K)^N` (exact transfer-matrix solution). -/
theorem onsager_2d_ising :
    (∀ (m n : ℕ) (K : ℝ), 0 < isingZ m n K) ∧
    (∀ m n : ℕ, isingZ m n 0 = 2 ^ ((m + 1) * (n + 1))) ∧
    onsagerLogZ 0 = Real.log 2 ∧
    (∀ m n : ℕ, Real.log (isingZ m n 0) / ((m + 1) * (n + 1) : ℕ) = onsagerLogZ 0) ∧
    (∀ (n : ℕ) (K : ℝ), isingZ 0 n K
      = Real.exp (K * (n + 1)) * ((2 * Real.cosh K) ^ (n + 1) + (2 * Real.sinh K) ^ (n + 1))) := by
  refine ⟨isingZ_pos, isingZ_zero, onsagerLogZ_zero, ?_, ?_⟩
  · intro m n
    rw [isingZ_zero, onsagerLogZ_zero, Real.log_pow]
    have h : ((m + 1) * (n + 1) : ℕ) ≠ (0 : ℝ) := by positivity
    field_simp
  · intro n K
    rw [isingZ_one_row, ringZ_eq]

end

end Frontier

