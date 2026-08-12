import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/
noncomputable def negPart (t : ℝ) : ℝ := max (-t) 0

lemma negPart_nonneg (t : ℝ) : 0 ≤ negPart t := le_max_right _ _

lemma negPart_neg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : negPart (-t) = t := by
  simp [negPart, ht]

/-- The one-particle density `ρ(x) = ∑ᵢ |uᵢ(x)|²` of a family of orbitals. -/
noncomputable def density {d n : ℕ} (u : Fin n → Space d → ℝ) (x : Space d) : ℝ :=
  ∑ i, (u i x) ^ 2

lemma density_nonneg {d n : ℕ} (u : Fin n → Space d → ℝ) (x : Space d) :
    0 ≤ density u x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The total kinetic energy `∑ᵢ ∫ |∇uᵢ|²` of a family of orbitals. -/
noncomputable def kineticEnergy {d n : ℕ} (u : Fin n → Space d → ℝ) : ℝ :=
  ∑ i, ∫ x, ‖gradient (u i) x‖ ^ 2

lemma kineticEnergy_nonneg {d n : ℕ} (u : Fin n → Space d → ℝ) : 0 ≤ kineticEnergy u :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun x => by positivity

/-- The potential energy `∑ᵢ ∫ V |uᵢ|² = ∫ V ρ` of a family of orbitals. -/
noncomputable def potentialEnergy {d n : ℕ} (V : Space d → ℝ) (u : Fin n → Space d → ℝ) : ℝ :=
  ∫ x, V x * density u x

/-- `u` is an `L²`-orthonormal family of real-valued functions on `ℝ^d`. -/
def OrthonormalFamily {d n : ℕ} (u : Fin n → Space d → ℝ) : Prop :=
  ∀ i j, (∫ x, u i x * u j x) = if i = j then 1 else 0

/-- Regularity conditions making a family of orbitals a legitimate `H¹` orthonormal family. -/
structure AdmissibleFamily {d n : ℕ} (u : Fin n → Space d → ℝ) : Prop where
  differentiable : ∀ i, Differentiable ℝ (u i)
  measurable : ∀ i, Measurable (u i)
  sq_integrable : ∀ i, Integrable (fun x => (u i x) ^ 2)
  grad_integrable : ∀ i, Integrable (fun x => ‖gradient (u i) x‖ ^ 2)
  orthonormal : OrthonormalFamily u

/-! ## The Lieb–Thirring inequality

We state the Lieb–Thirring inequality for `γ = 1` in its equivalent variational form: for
every `H¹`-orthonormal family `u` and every potential `V`, the sum of the one-particle
energies `∑ᵢ ⟨uᵢ, (-Δ + V) uᵢ⟩` is bounded below by `-L ∫ (V₋)^(1 + d/2)`.  By the min–max
principle this is exactly the statement that the sum of the negative eigenvalues of the
Schrödinger operator `-Δ + V` on `L²(ℝ^d)` is at least `-L ∫ (V₋)^(1 + d/2)`. -/
def LiebThirringEigenvalue (d : ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin n → Space d → ℝ) (V : Space d → ℝ),
    AdmissibleFamily u → Measurable V →
    Integrable (fun x => negPart (V x) ^ ((1 : ℝ) + d / 2)) →
    Integrable (fun x => V x * density u x) →
    -L * (∫ x, negPart (V x) ^ ((1 : ℝ) + d / 2)) ≤ kineticEnergy u + potentialEnergy V u

/-- The Lieb–Thirring kinetic energy inequality: for every `H¹`-orthonormal family, the
kinetic energy dominates `K ∫ ρ^(1 + 2/d)`, where `ρ` is the one-particle density.  This is
the form of the inequality that yields stability of matter. -/
def LiebThirringKinetic (d : ℕ) (K : ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin n → Space d → ℝ),
    AdmissibleFamily u →
    Integrable (fun x => density u x ^ ((1 : ℝ) + 2 / d)) →
    K * (∫ x, density u x ^ ((1 : ℝ) + 2 / d)) ≤ kineticEnergy u

/-- The kinetic-energy constant produced by the Legendre duality argument from a
Lieb–Thirring eigenvalue constant `L` in dimension `d`. -/
noncomputable def ltConst (d : ℕ) (L : ℝ) : ℝ :=
  ((d : ℝ) / (d + 2)) * (2 / (L * (d + 2))) ^ ((2 : ℝ) / d)

/-! ## Many-body Coulomb systems and stability of matter -/

/-- Configuration space of `N` electrons in `ℝ³`. -/
abbrev Config (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin 3)

/-- The position of the `i`-th electron in a configuration. -/
noncomputable def pos {N : ℕ} (x : Config N) (i : Fin N) : Space 3 :=
  WithLp.toLp 2 (fun k => x (i, k))

/-- The total Coulomb potential of `N` electrons and `K` nuclei of charges `Z` at
positions `R`: electron–nucleus attraction, electron–electron repulsion and
nucleus–nucleus repulsion. -/
noncomputable def coulombPotential {N K : ℕ} (Z : Fin K → ℝ) (R : Fin K → Space 3)
    (x : Config N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin K, -(Z j / dist (pos x i) (R j)))
    + (∑ i : Fin N, ∑ i' : Fin N, if i < i' then 1 / dist (pos x i) (pos x i') else 0)
    + (∑ j : Fin K, ∑ j' : Fin K, if j < j' then Z j * Z j' / dist (R j) (R j') else 0)

/-- The energy `⟨ψ, Hψ⟩` of a normalized many-body wave function `ψ`. -/
noncomputable def manyBodyEnergy {N K : ℕ} (Z : Fin K → ℝ) (R : Fin K → Space 3)
    (psi : Config N → ℝ) : ℝ :=
  (∫ x, ‖gradient psi x‖ ^ 2) + ∫ x, coulombPotential Z R x * (psi x) ^ 2

/-- Permuting the electron labels of a configuration. -/
noncomputable def permConfig {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Config N) : Config N :=
  WithLp.toLp 2 (fun p => x (σ p.1, p.2))

/-- Fermionic (antisymmetric) wave functions, as required by the Pauli principle. -/
def AntisymmetricWave {N : ℕ} (psi : Config N → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (x : Config N),
    psi (permConfig σ x) = (Equiv.Perm.sign σ : ℤ) * psi x

/-- **Stability of matter** with constant `C`: for every number `N` of electrons and `K` of
nuclei with charges bounded by `1`, and every normalized antisymmetric wave function, the
energy is bounded below by `-C (N + K)`.  The crucial point is that the bound is *linear*
in the number of particles. -/
def StabilityOfMatter (C : ℝ) : Prop :=
  ∀ (N K : ℕ) (Z : Fin K → ℝ) (R : Fin K → Space 3) (psi : Config N → ℝ),
    (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ 1) →
    Differentiable ℝ psi → Integrable (fun x => ‖gradient psi x‖ ^ 2) →
    (∫ x, (psi x) ^ 2) = 1 → AntisymmetricWave psi →
    Integrable (fun x => coulombPotential Z R x * (psi x) ^ 2) →
    -C * ((N : ℝ) + K) ≤ manyBodyEnergy Z R psi

/-- **Hardy's inequality** in `ℝ³`: `∫ |u|²/|x|² ≤ 4 ∫ |∇u|²` for `u ∈ H¹(ℝ³)`. -/
def HardyInequality : Prop :=
  ∀ (u : Space 3 → ℝ), Differentiable ℝ u → Integrable (fun x => (u x) ^ 2) →
    Integrable (fun x => ‖gradient u x‖ ^ 2) →
    Integrable (fun x => (u x) ^ 2 / ‖x‖ ^ 2) →
    (∫ x, (u x) ^ 2 / ‖x‖ ^ 2) ≤ 4 * ∫ x, ‖gradient u x‖ ^ 2

/-! ## Results -/

lemma ltConst_pos {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 < L) : 0 < ltConst d L := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hb : (0:ℝ) < 2 / (L * (d + 2)) := by positivity
  unfold ltConst
  positivity

/-- **Legendre duality reduction.**  The Lieb–Thirring bound on the sum of negative
eigenvalues implies the Lieb–Thirring kinetic energy inequality, with the explicit
(optimal, for this argument) constant `ltConst d L`. -/
theorem liebThirring_eigenvalue_to_kinetic {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 < L)
    (h : LiebThirringEigenvalue d L) : LiebThirringKinetic d (ltConst d L) := by
  intro n u hadm hint
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  set b : ℝ := 2 / (L * (d + 2)) with hbdef
  have hbpos : 0 < b := by rw [hbdef]; positivity
  set c : ℝ := b ^ ((2:ℝ)/d) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos hbpos _
  have hcd : c ^ ((d:ℝ)/2) = b := by
    rw [hcdef, ← Real.rpow_mul hbpos.le, show (2:ℝ)/d * ((d:ℝ)/2) = 1 by field_simp,
      Real.rpow_one]
  set A : ℝ := ∫ x, density u x ^ ((1:ℝ) + 2/d) with hAdef
  set V : Space d → ℝ := fun x => -(c * density u x ^ ((2:ℝ)/d)) with hVdef
  have hnp : ∀ x, negPart (V x) = c * density u x ^ ((2:ℝ)/d) := fun x =>
    negPart_neg_of_nonneg (by have := density_nonneg u x; positivity)
  have hpow : ∀ x, negPart (V x) ^ ((1:ℝ) + d/2)
      = c ^ ((1:ℝ) + d/2) * density u x ^ ((1:ℝ) + 2/d) := by
    intro x
    rw [hnp x, Real.mul_rpow hcpos.le (Real.rpow_nonneg (density_nonneg u x) _),
      ← Real.rpow_mul (density_nonneg u x), show (2:ℝ)/d * ((1:ℝ) + d/2) = (1:ℝ) + 2/d by
        field_simp; ring]
  have hsplit : ∀ x, density u x ^ ((1:ℝ)+2/d) = density u x ^ ((2:ℝ)/d) * density u x := by
    intro x
    rw [show (1:ℝ)+2/d = (2:ℝ)/d + 1 by ring,
      Real.rpow_add' (density_nonneg u x) (by positivity), Real.rpow_one]
  have hVr : ∀ x, V x * density u x = -c * density u x ^ ((1:ℝ)+2/d) := by
    intro x; rw [hsplit x, hVdef]; ring
  have hint1 : Integrable (fun x => negPart (V x) ^ ((1:ℝ) + (d:ℝ)/2)) := by
    refine (hint.const_mul (c ^ ((1:ℝ) + (d:ℝ)/2))).congr ?_
    filter_upwards with x
    exact (hpow x).symm
  have hint2 : Integrable (fun x => V x * density u x) := by
    refine (hint.const_mul (-c)).congr ?_
    filter_upwards with x
    exact (hVr x).symm
  have hrmeas : Measurable (fun x => density u x) :=
    Finset.measurable_sum _ (fun i _ => ((hadm.measurable i).pow_const 2))
  have hVmeas : Measurable V := ((hrmeas.pow_const _).const_mul c).neg
  have hI1 : (∫ x, negPart (V x) ^ ((1:ℝ) + (d:ℝ)/2)) = c ^ ((1:ℝ) + (d:ℝ)/2) * A := by
    simp_rw [hpow]; rw [integral_const_mul, ← hAdef]
  have hI2 : potentialEnergy V u = -c * A := by
    unfold potentialEnergy; simp_rw [hVr]; rw [integral_const_mul, ← hAdef]
  have hmain := h n u V hadm hVmeas hint1 hint2
  rw [hI1, hI2] at hmain
  have hcsplit : c ^ ((1:ℝ)+(d:ℝ)/2) = c * c ^ ((d:ℝ)/2) := by
    rw [Real.rpow_add' hcpos.le (by positivity), Real.rpow_one]
  have hLc : L * c ^ ((1:ℝ)+(d:ℝ)/2) = c * (2/((d:ℝ)+2)) := by
    rw [hcsplit, hcd, hbdef]; field_simp
  have hlt : ltConst d L = ((d:ℝ)/((d:ℝ)+2)) * c := by rw [hcdef, hbdef]; rfl
  rw [hlt]
  have hkey : c*A - L*(c ^ ((1:ℝ)+(d:ℝ)/2))*A = ((d:ℝ)/((d:ℝ)+2))*c*A := by
    rw [hLc]; field_simp; ring
  nlinarith [hmain, hkey]

/-- **Base case of stability of matter**: a system with no nuclear charge has nonnegative
energy, hence satisfies the stability bound for every `C ≥ 0`. -/
theorem stability_of_zero_charge {N K : ℕ} (Z : Fin K → ℝ) (R : Fin K → Space 3)
    (hZ : ∀ j, Z j = 0) (psi : Config N → ℝ) : 0 ≤ manyBodyEnergy Z R psi := by
  have hpot : ∀ x : Config N, 0 ≤ coulombPotential Z R x := by
    intro x
    unfold coulombPotential
    have h1 : (∑ i : Fin N, ∑ j : Fin K, -(Z j / dist (pos x i) (R j))) = 0 := by simp [hZ]
    have h3 : (∑ j : Fin K, ∑ j' : Fin K,
        if j < j' then Z j * Z j' / dist (R j) (R j') else 0) = 0 := by simp [hZ]
    rw [h1, h3]
    have h2 : (0:ℝ) ≤ ∑ i : Fin N, ∑ i' : Fin N,
        if i < i' then 1 / dist (pos x i) (pos x i') else 0 := by
      refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
      split <;> positivity
    linarith
  have hA : (0:ℝ) ≤ ∫ x : Config N, coulombPotential Z R x * (psi x)^2 :=
    integral_nonneg fun x => mul_nonneg (hpot x) (sq_nonneg _)
  have h0 : (0:ℝ) ≤ ∫ x : Config N, ‖gradient psi x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  unfold manyBodyEnergy
  linarith

/-- Pointwise arithmetic–geometric mean bound `v²/a ≤ (4Z)⁻¹ v²/a² + Z v²`, the elementary
ingredient turning Hardy's inequality into a lower bound on the hydrogenic energy. -/
lemma coulomb_le_of_hardy_pointwise {Z a : ℝ} (hZ : 0 < Z) (ha : 0 ≤ a) (v : ℝ) :
    v ^ 2 / a ≤ (4 * Z)⁻¹ * (v ^ 2 / a ^ 2) + Z * v ^ 2 := by
  rcases eq_or_lt_of_le ha with h | h
  · simp [← h]; positivity
  · have key : (4*Z)⁻¹ * (v^2/a^2) + Z*v^2 - v^2/a = v^2*(2*Z*a-1)^2/(4*Z*a^2) := by
      field_simp; ring
    nlinarith [div_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg (2*Z*a-1)))
      (by positivity : (0:ℝ) ≤ 4*Z*a^2)]

/-- **Base case of stability of matter: the hydrogenic atom.**  Given Hardy's inequality,
a single electron in the field of one nucleus of charge `Z` has energy at least `-Z²`. -/
theorem hydrogen_energy_lower_bound (hardy : HardyInequality) {Z : ℝ} (hZ : 0 < Z)
    (u : Space 3 → ℝ) (hu : Differentiable ℝ u)
    (hu2 : Integrable (fun x => (u x) ^ 2))
    (hg : Integrable (fun x => ‖gradient u x‖ ^ 2))
    (hh : Integrable (fun x => (u x) ^ 2 / ‖x‖ ^ 2))
    (hc : Integrable (fun x => (u x) ^ 2 / ‖x‖))
    (hnorm : (∫ x, (u x) ^ 2) = 1) :
    -Z ^ 2 ≤ (∫ x, ‖gradient u x‖ ^ 2) - Z * ∫ x, (u x) ^ 2 / ‖x‖ := by
  set T := ∫ x, ‖gradient u x‖ ^ 2 with hT
  set H := ∫ x, (u x) ^ 2 / ‖x‖ ^ 2 with hH
  set P := ∫ x, (u x) ^ 2 / ‖x‖ with hP
  have hRint : Integrable (fun x : Space 3 => (4*Z)⁻¹ * ((u x)^2/‖x‖^2) + Z*(u x)^2) :=
    (hh.const_mul _).add (hu2.const_mul _)
  have hpt : ∀ x : Space 3, (u x)^2/‖x‖ ≤ (4*Z)⁻¹ * ((u x)^2/‖x‖^2) + Z*(u x)^2 :=
    fun x => coulomb_le_of_hardy_pointwise hZ (norm_nonneg x) (u x)
  have hbound : P ≤ (4*Z)⁻¹ * H + Z * 1 := by
    have hm := integral_mono hc hRint hpt
    rwa [integral_add (hh.const_mul _) (hu2.const_mul _), integral_const_mul,
      integral_const_mul, hnorm] at hm
  have hHT : H ≤ 4 * T := hardy u hu hu2 hg hh
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have hstep : P ≤ T/Z + Z := by
    have h1 : (4*Z)⁻¹ * H ≤ (4*Z)⁻¹ * (4*T) :=
      mul_le_mul_of_nonneg_left hHT (by positivity)
    have h2 : (4*Z)⁻¹ * (4*T) = T/Z := by field_simp
    linarith
  have h2 : Z * P ≤ Z * (T/Z + Z) := mul_le_mul_of_nonneg_left hstep hZ.le
  have h3 : Z * (T/Z + Z) = T + Z^2 := by field_simp
  linarith

/-- **Lieb–Thirring and stability of matter.**

1. The Lieb–Thirring bound on sums of negative eigenvalues of `-Δ + V` on `L²(ℝ^d)`
   reduces, by Legendre duality, to the kinetic-energy form of the Lieb–Thirring
   inequality with the explicit positive constant `ltConst d L`.
2. Base case of stability of matter: a system of `N` electrons and `K` nuclei carrying no
   charge has nonnegative energy, so it obeys the stability bound `E ≥ -C (N + K)`.
3. Base case of stability of matter: given Hardy's inequality, a hydrogenic atom of nuclear
   charge `Z > 0` has energy at least `-Z²`. -/
theorem lieb_thirring_stability :
    (∀ (d : ℕ) (L : ℝ), 0 < d → 0 < L → LiebThirringEigenvalue d L →
        0 < ltConst d L ∧ LiebThirringKinetic d (ltConst d L)) ∧
    (∀ (C : ℝ), 0 ≤ C → ∀ (N K : ℕ) (Z : Fin K → ℝ) (R : Fin K → Space 3)
        (psi : Config N → ℝ), (∀ j, Z j = 0) →
        -C * ((N : ℝ) + K) ≤ manyBodyEnergy Z R psi) ∧
    (HardyInequality → ∀ (Z : ℝ), 0 < Z → ∀ (u : Space 3 → ℝ), Differentiable ℝ u →
        Integrable (fun x => (u x) ^ 2) → Integrable (fun x => ‖gradient u x‖ ^ 2) →
        Integrable (fun x => (u x) ^ 2 / ‖x‖ ^ 2) → Integrable (fun x => (u x) ^ 2 / ‖x‖) →
        (∫ x, (u x) ^ 2) = 1 →
        -Z ^ 2 ≤ (∫ x, ‖gradient u x‖ ^ 2) - Z * ∫ x, (u x) ^ 2 / ‖x‖) := by
  refine ⟨fun d L hd hL h => ⟨ltConst_pos hd hL, liebThirring_eigenvalue_to_kinetic hd hL h⟩,
    ?_, fun hardy Z hZ u hu hu2 hg hh hc hnorm =>
      hydrogen_energy_lower_bound hardy hZ u hu hu2 hg hh hc hnorm⟩
  intro C hC N K Z R psi hZ
  have h0 : 0 ≤ manyBodyEnergy Z R psi := stability_of_zero_charge Z R hZ psi
  have : -C * ((N : ℝ) + K) ≤ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) + K := by positivity
    nlinarith
  linarith

end Frontier

#print axioms Frontier.lieb_thirring_stability

