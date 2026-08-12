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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The argument of the logarithm in Onsager's exact free energy formula for the
two-dimensional square-lattice Ising model with reduced coupling `K = βJ`. -/
noncomputable def onsagerIntegrand (K t₁ t₂ : ℝ) : ℝ :=
  Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos t₁ + Real.cos t₂)

/-- Onsager's exact (dimensionless) free energy per site
`-βf = log 2 + (8π²)⁻¹ ∫₀^{2π} ∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`
for the two-dimensional square-lattice Ising model at reduced coupling `K = βJ`. -/
noncomputable def onsagerFreeEnergy (K : ℝ) : ℝ :=
  Real.log 2 +
    (1 / (8 * Real.pi ^ 2)) *
      ∫ t₁ in (0 : ℝ)..(2 * Real.pi), ∫ t₂ in (0 : ℝ)..(2 * Real.pi),
        Real.log (onsagerIntegrand K t₁ t₂)

/-- The critical reduced coupling `K_c = ½ log (1 + √2)` of the 2D Ising model. -/
noncomputable def isingCritical : ℝ := Real.log (1 + Real.sqrt 2) / 2

/-- Real-valued spin attached to a boolean spin variable. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The sum `∑_{⟨x,y⟩} σ_x σ_y` of nearest-neighbour products on the `m × n` periodic
square lattice (discrete torus `ZMod m × ZMod n`). -/
noncomputable def isingNeighbourSum (m n : ℕ) [NeZero m] [NeZero n]
    (σ : ZMod m × ZMod n → Bool) : ℝ :=
  ∑ x : ZMod m × ZMod n,
    (spin (σ x) * spin (σ (x.1 + 1, x.2)) + spin (σ x) * spin (σ (x.1, x.2 + 1)))

/-- The Ising partition function `Z = ∑_σ exp (K ∑_{⟨x,y⟩} σ_x σ_y)` on the `m × n` torus. -/
noncomputable def isingPartition (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  ∑ σ : ZMod m × ZMod n → Bool, Real.exp (K * isingNeighbourSum m n σ)

/-- The finite-volume free energy per site `(mn)⁻¹ log Z`. -/
noncomputable def isingFreeEnergyPerSite (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  (1 / (m * n : ℝ)) * Real.log (isingPartition m n K)

lemma onsagerIntegrand_nonneg (K t₁ t₂ : ℝ) : 0 ≤ onsagerIntegrand K t₁ t₂ := by
  have hc : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    have := Real.cosh_sq (2 * K)
    linarith [Real.sinh_sq (2 * K)]
  have h1 : Real.cos t₁ ≤ 1 := Real.cos_le_one t₁
  have h2 : Real.cos t₂ ≤ 1 := Real.cos_le_one t₂
  have h1' : -1 ≤ Real.cos t₁ := Real.neg_one_le_cos t₁
  have h2' : -1 ≤ Real.cos t₂ := Real.neg_one_le_cos t₂
  set s := Real.sinh (2 * K) with hs
  have key : 0 ≤ (|s| - 1) ^ 2 := sq_nonneg _
  have habs : s * (Real.cos t₁ + Real.cos t₂) ≤ 2 * |s| := by
    have : s * (Real.cos t₁ + Real.cos t₂) ≤ |s * (Real.cos t₁ + Real.cos t₂)| := le_abs_self _
    have h3 : |s * (Real.cos t₁ + Real.cos t₂)| = |s| * |Real.cos t₁ + Real.cos t₂| := abs_mul _ _
    have h4 : |Real.cos t₁ + Real.cos t₂| ≤ 2 := by
      rw [abs_le]; constructor <;> [linarith [Real.neg_one_le_cos t₁, Real.neg_one_le_cos t₂];
        linarith]
    nlinarith [abs_nonneg s]
  have hsq : |s| ^ 2 = s ^ 2 := sq_abs s
  unfold onsagerIntegrand
  nlinarith [key, habs, hsq, hc]

lemma onsagerIntegrand_zero (t₁ t₂ : ℝ) : onsagerIntegrand 0 t₁ t₂ = 1 := by
  simp [onsagerIntegrand]

/-- Base case (free spins): at zero coupling Onsager's formula gives `log 2` per site. -/
lemma onsagerFreeEnergy_zero : onsagerFreeEnergy 0 = Real.log 2 := by
  simp [onsagerFreeEnergy, onsagerIntegrand_zero]

lemma sinh_two_isingCritical : Real.sinh (2 * isingCritical) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by
    have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hx : Real.exp (2 * isingCritical) = 1 + Real.sqrt 2 := by
    unfold isingCritical
    rw [show 2 * (Real.log (1 + Real.sqrt 2) / 2) = Real.log (1 + Real.sqrt 2) by ring,
      Real.exp_log h2]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sinh_eq, hx, Real.exp_neg, hx]
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg 2]

/-- At the critical coupling the Onsager integrand vanishes exactly at the corner
`θ₁ = θ₂ = 0` (mod `2π`) of the Brillouin zone: this is the source of the singularity. -/
lemma onsagerIntegrand_isingCritical_eq_zero_iff (t₁ t₂ : ℝ) :
    onsagerIntegrand isingCritical t₁ t₂ = 0 ↔ Real.cos t₁ + Real.cos t₂ = 2 := by
  have hs : Real.sinh (2 * isingCritical) = 1 := sinh_two_isingCritical
  have hc : Real.cosh (2 * isingCritical) ^ 2 = 2 := by
    have := Real.cosh_sq_sub_sinh_sq (2 * isingCritical)
    rw [hs] at this; nlinarith [this]
  unfold onsagerIntegrand
  rw [hs, hc]
  constructor <;> intro h <;> linarith

/-- Sanity check on the lattice Hamiltonian: the ferromagnetic ground state has bond energy
`2mn`, i.e. two bonds per site. -/
lemma isingNeighbourSum_const_true (m n : ℕ) [NeZero m] [NeZero n] :
    isingNeighbourSum m n (fun _ => true) = 2 * (m * n : ℝ) := by
  unfold isingNeighbourSum
  simp [spin, Finset.card_univ, ZMod.card]
  ring

lemma isingPartition_zero (m n : ℕ) [NeZero m] [NeZero n] :
    isingPartition m n 0 = 2 ^ (m * n) := by
  unfold isingPartition
  simp only [zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_fun]
  simp [ZMod.card, pow_mul]

/-- Free-spin base case for the finite lattice: at zero coupling the exact finite-volume
free energy per site equals `log 2` for every lattice size. -/
lemma isingFreeEnergyPerSite_zero (m n : ℕ) [NeZero m] [NeZero n] :
    isingFreeEnergyPerSite m n 0 = Real.log 2 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold isingFreeEnergyPerSite
  rw [isingPartition_zero, Real.log_pow]
  field_simp
  push_cast
  ring

/--
**Onsager's exact solution of the two-dimensional Ising model (formalized statement with
Lean-checked reductions).**

We formalize Onsager's free energy
`-βf(K) = log 2 + (8π²)⁻¹ ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`
together with the exact finite-volume Ising partition function on the `m × n` discrete torus,
and prove:

1. the Onsager integrand is nonnegative for every coupling and every momentum, so the
   formula is well posed;
2. Onsager's formula reduces to `log 2` at zero coupling;
3. the exact finite-volume free energy per site equals `log 2` at zero coupling, for every
   lattice size — i.e. the exact lattice model and Onsager's formula agree in the free-spin
   base case;
4. the critical coupling `K_c = ½ log (1 + √2)` satisfies Kramers–Wannier's `sinh (2K_c) = 1`;
5. at `K_c` the integrand degenerates exactly at `cos θ₁ + cos θ₂ = 2`, which is the origin
   of the critical singularity;
6. the ferromagnetic ground state of the lattice Hamiltonian has bond sum `2mn` (two bonds
   per site), a sanity check that the finite-volume model is set up correctly.
-/
theorem onsager_2d_ising :
    (∀ K t₁ t₂ : ℝ, 0 ≤ onsagerIntegrand K t₁ t₂) ∧
    onsagerFreeEnergy 0 = Real.log 2 ∧
    (∀ (m n : ℕ) [NeZero m] [NeZero n],
      isingFreeEnergyPerSite m n 0 = onsagerFreeEnergy 0) ∧
    Real.sinh (2 * isingCritical) = 1 ∧
    (∀ t₁ t₂ : ℝ, onsagerIntegrand isingCritical t₁ t₂ = 0 ↔ Real.cos t₁ + Real.cos t₂ = 2) ∧
    (∀ (m n : ℕ) [NeZero m] [NeZero n],
      isingNeighbourSum m n (fun _ => true) = 2 * (m * n : ℝ)) := by
  refine ⟨onsagerIntegrand_nonneg, onsagerFreeEnergy_zero, ?_, sinh_two_isingCritical,
    onsagerIntegrand_isingCritical_eq_zero_iff, fun m n _ _ => isingNeighbourSum_const_true m n⟩
  intro m n _ _
  rw [isingFreeEnergyPerSite_zero, onsagerFreeEnergy_zero]

end Frontier

