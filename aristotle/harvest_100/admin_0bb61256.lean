/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Setting

We work with the standard "conjugacy" formulation of KAM theory.  The phase space is an
arbitrary type `P`, the `n`-dimensional torus is modelled by its universal cover
`Fin n → ℝ` (all objects below are invariant under the choice of representative, so
nothing is lost), and a *torus with rotation vector `ω`* for a dynamical system
`f : P → P` is an embedding `Ψ : (Fin n → ℝ) → P` satisfying the conjugacy equation

  `f (Ψ θ) = Ψ (θ + ω)`  for all `θ`,

i.e. `f` restricted to the image of `Ψ` is the rigid rotation by `ω`.
-/

/-- `IsInvariantTorus n f ω Ψ` : the parametrised torus `Ψ` is invariant under the
dynamics `f` and the induced motion on it is the rigid rotation by the frequency
vector `ω`. -/
def IsInvariantTorus {P : Type*} {n : ℕ} (f : P → P) (ω : Fin n → ℝ)
    (Ψ : (Fin n → ℝ) → P) : Prop :=
  ∀ θ : Fin n → ℝ, f (Ψ θ) = Ψ (θ + ω)

/-! ## The integrable (unperturbed) base case

For an integrable system written in action–angle variables `(θ, I)`, the time-`t` map is
`(θ, I) ↦ (θ + t • ω I, I)`.  Every level set of the action is then an invariant torus,
carrying a rigid rotation with frequency `t • ω I₀`.  This is the base case `ε = 0` of KAM.
-/

/-- The time-`t` map of an integrable system in action–angle variables. -/
def integrableFlow {n : ℕ} (ω : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) → ((Fin n → ℝ) × (Fin n → ℝ)) :=
  fun p => (p.1 + t • ω p.2, p.2)

/-- **Base case of KAM.** For the unperturbed integrable system every action level set
`{I = I₀}` is an invariant torus of the time-`t` map, with rotation vector `t • ω I₀`. -/
theorem integrable_isInvariantTorus {n : ℕ} (ω : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ)
    (I₀ : Fin n → ℝ) :
    IsInvariantTorus (integrableFlow ω t) (t • ω I₀) (fun θ => (θ, I₀)) := by
  intro θ
  simp [integrableFlow]

/-- Any point of an invariant torus stays on the torus: the image of the parametrisation
is an invariant set. -/
theorem mapsTo_range_of_isInvariantTorus {P : Type*} {n : ℕ} {f : P → P} {ω : Fin n → ℝ}
    {Ψ : (Fin n → ℝ) → P} (h : IsInvariantTorus f ω Ψ) :
    Set.MapsTo f (Set.range Ψ) (Set.range Ψ) := by
  rintro _ ⟨θ, rfl⟩
  exact ⟨θ + ω, (h θ).symm⟩

/-! ## Persistence under perturbation

The analytic heart of KAM theory is the construction, for a Diophantine frequency `ω`, of a
*KAM operator* `T ε` on a Banach space `E` of torus parametrisations (encoded here through
a map `Ψ : E → ((Fin n → ℝ) → P)` sending a parameter to the corresponding embedding) whose
fixed points solve the conjugacy equation, and which is a contraction depending Lipschitz-
continuously on the size `ε` of the perturbation.  Granting that reduction, persistence of
the invariant torus — together with the quantitative statement that the persisting torus is
`O(ε)`-close to the unperturbed one — follows from the Banach fixed point theorem.

That last step is what `Frontier.kam_theorem` below states and proves.
-/

/-- **KAM theorem (persistence of invariant tori), Banach-fixed-point form.**

Let `f ε : P → P` be a family of dynamical systems, `ε` measuring the size of the
perturbation of the integrable system `f 0`.  Suppose the conjugacy equation for a torus with
frequency vector `ω` has been reduced (as in the classical KAM scheme) to a fixed point
problem `T ε u = u` on a Banach space `E` of parametrisations `u ↦ Ψ u`, where

* `hfix`   : fixed points of `T ε` are invariant tori of `f ε` with frequency `ω`;
* `hlip`   : each `T ε` is a `K`-contraction, `K < 1`;
* `hzero`  : the unperturbed problem is solved by the reference parametrisation `u = 0`
             (`T 0 0 = 0`), which by `hfix` is an invariant torus of `f 0`;
* `hpert`  : the operator moves by at most `C * |ε|` when the perturbation is switched on.

Then for *every* `ε` the invariant torus persists: there is a parametrisation `u` whose torus
`Ψ u` is invariant under `f ε` and carries the same rotation vector `ω`, and it is
`C * |ε| / (1 - K)`-close to the unperturbed torus.  In particular the distance tends to `0`
as `ε → 0`.

The Banach fixed point theorem (`ContractingWith.fixedPoint_isFixedPt` together with the
a priori estimate `ContractingWith.dist_fixedPoint_le`) is exactly the Mathlib input that
closes the argument. -/
theorem kam_theorem {P : Type*} {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → P → P) (ω : Fin n → ℝ) (Ψ : E → ((Fin n → ℝ) → P))
    (T : ℝ → E → E) (K : NNReal) (C : ℝ) [CompleteSpace E]
    (hK : K < 1)
    (hlip : ∀ ε : ℝ, LipschitzWith K (T ε))
    (hfix : ∀ (ε : ℝ) (u : E), T ε u = u → IsInvariantTorus (f ε) ω (Ψ u))
    (hzero : T 0 0 = 0)
    (hpert : ∀ (ε : ℝ) (u : E), ‖T ε u - T 0 u‖ ≤ C * |ε|) :
    ∀ ε : ℝ, ∃ u : E, IsInvariantTorus (f ε) ω (Ψ u) ∧ ‖u‖ ≤ C * |ε| / (1 - K) := by
  intro ε
  have hcon : ContractingWith K (T ε) := ⟨hK, hlip ε⟩
  set u := hcon.fixedPoint
  have hufix : T ε u = u := hcon.fixedPoint_isFixedPt
  refine ⟨u, hfix ε u hufix, ?_⟩
  have h0 : dist (0 : E) u ≤ dist (0 : E) (T ε 0) / (1 - K) := hcon.dist_fixedPoint_le 0
  have hnum : dist (0 : E) (T ε 0) ≤ C * |ε| := by
    have := hpert ε 0
    rw [hzero, sub_zero] at this
    simpa [dist_eq_norm, norm_sub_rev] using this
  have hK' : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  calc ‖u‖ = dist (0 : E) u := by simp [dist_eq_norm]
    _ ≤ dist (0 : E) (T ε 0) / (1 - K) := h0
    _ ≤ C * |ε| / (1 - K) := by
        gcongr

/-! ## Small divisors

The hypothesis `hlip` above is exactly what the classical KAM scheme establishes, and its
crucial ingredient is the solvability of the *homological equation* with control on the
small divisors `⟨k, ω⟩`.  We record the corresponding elementary estimate for a Diophantine
frequency vector. -/

/-- The `ℓ¹`-norm of an integer frequency multi-index, as a real number. -/
noncomputable def multiIndexNorm {n : ℕ} (k : Fin n → ℤ) : ℝ := ∑ i, |(k i : ℝ)|

/-- `ω` is `(γ, τ)`-Diophantine: its resonances `⟨k, ω⟩` are bounded away from `0`
polynomially in the size of `k`. -/
def Diophantine {n : ℕ} (ω : Fin n → ℝ) (γ τ : ℝ) : Prop :=
  0 < γ ∧ ∀ k : Fin n → ℤ, k ≠ 0 → γ / (multiIndexNorm k) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|

theorem multiIndexNorm_pos {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < multiIndexNorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext fun i => by simpa using h i)
  have hpos : 0 < |(k i : ℝ)| := by
    simpa using (Int.cast_ne_zero (α := ℝ)).2 hi
  refine Finset.sum_pos' (fun j _ => abs_nonneg _) ⟨i, Finset.mem_univ i, hpos⟩

/-- **Small divisor estimate.**  For a `(γ, τ)`-Diophantine frequency vector `ω` and a
nonzero multi-index `k`, the `k`-th Fourier coefficient equation `⟨k, ω⟩ * x = c` coming from
the homological equation is uniquely solvable, and the solution loses only the polynomial
factor `‖k‖^τ / γ` in size. -/
theorem small_divisor_bound {n : ℕ} {ω : Fin n → ℝ} {γ τ : ℝ} (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) (c : ℝ) :
    ∃ x : ℝ, (∑ i, (k i : ℝ) * ω i) * x = c ∧ |x| ≤ |c| * (multiIndexNorm k) ^ τ / γ := by
  obtain ⟨hγ, hdio⟩ := hω
  set d : ℝ := ∑ i, (k i : ℝ) * ω i with hd
  have hnpos : 0 < multiIndexNorm k := multiIndexNorm_pos hk
  have hpow : 0 < (multiIndexNorm k) ^ τ := Real.rpow_pos_of_pos hnpos τ
  have hlow : 0 < γ / (multiIndexNorm k) ^ τ := div_pos hγ hpow
  have habs : γ / (multiIndexNorm k) ^ τ ≤ |d| := hdio k hk
  have hdpos : 0 < |d| := lt_of_lt_of_le hlow habs
  have hdne : d ≠ 0 := by
    intro h
    rw [h] at hdpos
    simp at hdpos
  refine ⟨c / d, by field_simp, ?_⟩
  have h1 : |c / d| = |c| / |d| := abs_div c d
  have h2 : |c| / |d| ≤ |c| / (γ / (multiIndexNorm k) ^ τ) :=
    div_le_div_of_nonneg_left (abs_nonneg c) hlow habs
  have h3 : |c| / (γ / (multiIndexNorm k) ^ τ) = |c| * (multiIndexNorm k) ^ τ / γ := by
    field_simp
  rw [h1, ← h3]
  exact h2

end Frontier

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

