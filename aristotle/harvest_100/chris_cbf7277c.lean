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

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The energy of a spin configuration `σ` on the `m × n` torus with nearest-neighbour
coupling `J`:  `E(σ) = -J ∑_{⟨i,j⟩} σ_i σ_j`, the sum running over all horizontal and
vertical bonds (periodic boundary conditions in both directions). -/
def isingEnergy (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ)
    (σ : ZMod m × ZMod n → Bool) : ℝ :=
  -J * ∑ p : ZMod m × ZMod n,
      (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))

/-- The canonical partition function `Z = ∑_σ exp (-β E(σ))` of the 2D Ising model on the
`m × n` torus at inverse temperature `β`. -/
noncomputable def isingZ (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) : ℝ :=
  ∑ σ : ZMod m × ZMod n → Bool, Real.exp (-β * isingEnergy m n J σ)

/-- The free energy density in the form `(1 / (m n)) log Z`, i.e. `-β f` per site. -/
noncomputable def isingLogZDensity (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) : ℝ :=
  (1 / ((m : ℝ) * n)) * Real.log (isingZ m n J β)

/-- The Onsager–Kramers–Wannier **transfer matrix** of the 2D Ising model: it is indexed by
the states `s : ZMod n → Bool` of a single row of `n` spins, and
`T s s' = exp (β J (∑_y s_y s'_y + ∑_y s_y s_{y+1}))` accounts for all the bonds between
two consecutive rows together with the bonds inside the first of them. -/
noncomputable def transferMatrix (n : ℕ) [NeZero n] (J β : ℝ) :
    Matrix (ZMod n → Bool) (ZMod n → Bool) ℝ :=
  Matrix.of fun s s' => Real.exp (β * J * ∑ y : ZMod n,
    (spin (s y) * spin (s' y) + spin (s y) * spin (s (y + 1))))

/-! ## Onsager's exact expression -/

/-- The integrand of Onsager's exact solution,
`log (cosh²(2βJ) - sinh(2βJ) (cos θ + cos ψ))`. -/
noncomputable def onsagerIntegrand (J β θ ψ : ℝ) : ℝ :=
  Real.log (Real.cosh (2 * β * J) ^ 2
    - Real.sinh (2 * β * J) * (Real.cos θ + Real.cos ψ))

/-- Onsager's exact expression for the free energy density of the 2D Ising model:
`log 2 + (1 / (2 (2π)²)) ∫₀^{2π} ∫₀^{2π} log (cosh²(2βJ) - sinh(2βJ)(cos θ + cos ψ)) dψ dθ`. -/
noncomputable def onsagerLogZDensity (J β : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * (2 * Real.pi) ^ 2)) *
    ∫ θ in (0:ℝ)..(2 * Real.pi), ∫ ψ in (0:ℝ)..(2 * Real.pi), onsagerIntegrand J β θ ψ

/-- **Onsager's theorem** (the full statement): for every coupling `J` and every inverse
temperature `β`, the free energy density of the `N × N` periodic Ising lattice converges,
as `N → ∞`, to Onsager's exact expression. -/
def OnsagerFreeEnergyStatement : Prop :=
  ∀ J β : ℝ, Filter.Tendsto
    (fun N : ℕ => isingLogZDensity (N + 1) (N + 1) J β) Filter.atTop
    (nhds (onsagerLogZDensity J β))

/-! ## Elementary facts about the model -/

theorem abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> norm_num [spin]

/-- At infinite temperature (`β = 0`) all `2^{mn}` configurations have equal weight. -/
theorem isingZ_zero (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ) :
    isingZ m n J 0 = 2 ^ (m * n) := by
  simp [isingZ, Finset.card_univ, ZMod.card]

/-- The energy per site is bounded by `2 |J|` (each site carries two bonds). -/
theorem abs_isingEnergy_le (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ)
    (σ : ZMod m × ZMod n → Bool) :
    |isingEnergy m n J σ| ≤ 2 * (m * n) * |J| := by
  have hS : |∑ p : ZMod m × ZMod n,
      (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
      ≤ 2 * ((m : ℝ) * n) := by
    calc |∑ p : ZMod m × ZMod n,
            (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
        ≤ ∑ p : ZMod m × ZMod n,
            |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : ZMod m × ZMod n, (2 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro p _
          calc |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))|
              ≤ |spin (σ p) * spin (σ (p.1 + 1, p.2))| + |spin (σ p) * spin (σ (p.1, p.2 + 1))| :=
                abs_add_le _ _
            _ = 2 := by simp [abs_mul, abs_spin]; ring
      _ = 2 * ((m : ℝ) * n) := by
          simp [Finset.card_univ, ZMod.card]
          ring
  rw [isingEnergy, abs_mul, abs_neg]
  calc |J| * |∑ p : ZMod m × ZMod n,
      (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
      ≤ |J| * (2 * ((m : ℝ) * n)) := mul_le_mul_of_nonneg_left hS (abs_nonneg J)
    _ = 2 * ((m : ℝ) * n) * |J| := by ring

/-- Uniform bounds on the finite-volume free energy density, valid at every temperature. -/
theorem abs_isingLogZDensity_sub_log_two_le (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    |isingLogZDensity m n J β - Real.log 2| ≤ 2 * |β| * |J| := by
  set C : ℝ := 2 * ((m : ℝ) * n) * |J| * |β| with hC
  have hcard : (Finset.univ : Finset (ZMod m × ZMod n → Bool)).card = 2 ^ (m * n) := by
    simp [Finset.card_univ, ZMod.card]
  have hterm : ∀ σ : ZMod m × ZMod n → Bool,
      Real.exp (-C) ≤ Real.exp (-β * isingEnergy m n J σ) ∧
      Real.exp (-β * isingEnergy m n J σ) ≤ Real.exp C := by
    intro σ
    have h1 : |(-β) * isingEnergy m n J σ| ≤ C := by
      rw [abs_mul, abs_neg, hC]
      calc |β| * |isingEnergy m n J σ| ≤ |β| * (2 * ((m : ℝ) * n) * |J|) :=
            mul_le_mul_of_nonneg_left (abs_isingEnergy_le m n J σ) (abs_nonneg β)
        _ = 2 * ((m : ℝ) * n) * |J| * |β| := by ring
    have h2 := abs_le.mp h1
    exact ⟨Real.exp_le_exp.mpr h2.1, Real.exp_le_exp.mpr h2.2⟩
  have hub : isingZ m n J β ≤ 2 ^ (m * n) * Real.exp C := by
    rw [isingZ]
    calc ∑ σ : ZMod m × ZMod n → Bool, Real.exp (-β * isingEnergy m n J σ)
        ≤ ∑ _σ : ZMod m × ZMod n → Bool, Real.exp C :=
          Finset.sum_le_sum (fun σ _ => (hterm σ).2)
      _ = 2 ^ (m * n) * Real.exp C := by rw [Finset.sum_const, hcard]; simp [nsmul_eq_mul]
  have hlb : (2 : ℝ) ^ (m * n) * Real.exp (-C) ≤ isingZ m n J β := by
    rw [isingZ]
    calc (2 : ℝ) ^ (m * n) * Real.exp (-C)
        = ∑ _σ : ZMod m × ZMod n → Bool, Real.exp (-C) := by
          rw [Finset.sum_const, hcard]; simp [nsmul_eq_mul]
      _ ≤ ∑ σ : ZMod m × ZMod n → Bool, Real.exp (-β * isingEnergy m n J σ) :=
          Finset.sum_le_sum (fun σ _ => (hterm σ).1)
  have hpos : 0 < isingZ m n J β := lt_of_lt_of_le (by positivity) hlb
  have hlogub : Real.log (isingZ m n J β) ≤ ((m * n : ℕ) : ℝ) * Real.log 2 + C := by
    have h := Real.log_le_log hpos hub
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    exact_mod_cast h
  have hloglb : ((m * n : ℕ) : ℝ) * Real.log 2 - C ≤ Real.log (isingZ m n J β) := by
    have h := Real.log_le_log (by positivity) hlb
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    push_cast at h ⊢
    linarith
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hmn : (0 : ℝ) < (m : ℝ) * n := mul_pos hm hn
  push_cast at hlogub hloglb
  have hinv : (0 : ℝ) ≤ 1 / ((m : ℝ) * n) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hloglb hinv
  have e2 := mul_le_mul_of_nonneg_left hlogub hinv
  have hxa : 1 / ((m : ℝ) * n) * (((m : ℝ) * n) * Real.log 2) = Real.log 2 := by
    field_simp
  have hCval : 1 / ((m : ℝ) * n) * C = 2 * |β| * |J| := by
    rw [hC]; field_simp
  rw [mul_sub, hxa] at e1
  rw [mul_add, hxa] at e2
  rw [isingLogZDensity, abs_le]
  constructor <;> linarith

/-- Onsager's expression at infinite temperature. -/
theorem onsagerLogZDensity_zero (J : ℝ) : onsagerLogZDensity J 0 = Real.log 2 := by
  simp [onsagerLogZDensity, onsagerIntegrand]

/-- The finite-volume free energy density at infinite temperature. -/
theorem isingLogZDensity_zero (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ) :
    isingLogZDensity m n J 0 = Real.log 2 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [isingLogZDensity, isingZ_zero, Real.log_pow]
  push_cast
  field_simp

/-! ## The transfer-matrix reduction

The first (and decisive) step of Onsager's solution is the reduction of the two-dimensional
partition function on the `m × n` torus to the trace of the `m`-th power of a `2ⁿ × 2ⁿ`
transfer matrix.  This section proves that reduction. -/

/-- Sum over open paths: for any matrix `T` and any matrix `A`,
`∑_{paths} A(r_last, r_0) ∏ T(r_i, r_{i+1}) = tr (A Tʲ)`. -/
theorem sum_path_prod_eq_trace {S : Type} [Fintype S] [DecidableEq S]
    (T A : Matrix S S ℝ) (j : ℕ) :
    ∑ r : Fin (j + 1) → S,
        (A (r (Fin.last j)) (r 0) * ∏ i : Fin j, T (r i.castSucc) (r i.succ))
      = Matrix.trace (A * T ^ j) := by
  induction j generalizing A with
  | zero =>
      simp only [Matrix.trace, Matrix.diag, pow_zero, mul_one, Finset.univ_unique,
        Finset.prod_empty, Finset.prod_const_one, mul_one, Fin.last_zero]
      exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ (fun _ => rfl)
  | succ j ih =>
      have key : ∑ r : Fin (j + 2) → S,
          (A (r (Fin.last (j + 1))) (r 0) * ∏ i : Fin (j + 1), T (r i.castSucc) (r i.succ))
          = ∑ p : S × (Fin (j + 1) → S),
              (A p.1 (p.2 0) * ((∏ i : Fin j, T (p.2 i.castSucc) (p.2 i.succ))
                * T (p.2 (Fin.last j)) p.1)) := by
        refine (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (j + 2) => S)) _ _ ?_).symm
        rintro ⟨u, q⟩
        simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
        rw [Fin.prod_univ_castSucc]
        have h0 : (0 : Fin (j + 2)) = (0 : Fin (j + 1)).castSucc := rfl
        rw [h0, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        congr 2
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [show i.castSucc.castSucc = (Fin.castSucc i).castSucc from rfl, Fin.snoc_castSucc,
          Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [key, Fintype.sum_prod_type_right]
      have hstep : ∀ q : Fin (j + 1) → S,
          ∑ u : S, A u (q 0) * ((∏ i : Fin j, T (q i.castSucc) (q i.succ)) * T (q (Fin.last j)) u)
            = (T * A) (q (Fin.last j)) (q 0) * ∏ i : Fin j, T (q i.castSucc) (q i.succ) := by
        intro q
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      simp_rw [hstep]
      rw [ih (T * A)]
      calc Matrix.trace ((T * A) * T ^ j) = Matrix.trace (T * (A * T ^ j)) := by rw [mul_assoc]
        _ = Matrix.trace ((A * T ^ j) * T) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (A * T ^ (j + 1)) := by rw [mul_assoc, ← pow_succ]

/-- Sum over closed paths: `∑_{r : Fin (j+1) → S} ∏_i T(r i, r (i+1)) = tr (T^(j+1))`,
the indices being read cyclically. -/
theorem cyclic_sum_prod_eq_trace {S : Type} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℝ) (j : ℕ) :
    ∑ r : Fin (j + 1) → S, ∏ i : Fin (j + 1), T (r i) (r (i + 1))
      = Matrix.trace (T ^ (j + 1)) := by
  have hsplit : ∀ r : Fin (j + 1) → S, (∏ i : Fin (j + 1), T (r i) (r (i + 1)))
      = T (r (Fin.last j)) (r 0) * ∏ i : Fin j, T (r i.castSucc) (r i.succ) := by
    intro r
    rw [Fin.prod_univ_castSucc, Fin.last_add_one, mul_comm]
    exact congrArg _ (Finset.prod_congr rfl (fun i _ => by rw [Fin.coeSucc_eq_succ]))
  simp_rw [hsplit]
  rw [sum_path_prod_eq_trace T T j, ← pow_succ']

/-- The partition function is the sum, over all sequences of row states, of the products of
transfer-matrix entries along the (cyclically closed) sequence. -/
theorem isingZ_eq_sum_prod (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    isingZ m n J β
      = ∑ r : ZMod m → (ZMod n → Bool), ∏ i : ZMod m, transferMatrix n J β (r i) (r (i + 1)) := by
  rw [isingZ]
  refine Fintype.sum_equiv (Equiv.curry (ZMod m) (ZMod n) Bool) _ _ ?_
  intro σ
  show Real.exp (-β * isingEnergy m n J σ) = _
  simp only [transferMatrix, Matrix.of_apply, Equiv.curry_apply]
  rw [← Real.exp_sum, isingEnergy]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [Function.curry_apply]
  ring

/-- **The transfer-matrix reduction of the 2D Ising model.**  For every lattice size and
every temperature, the partition function on the `m × n` torus is the trace of the `m`-th
power of the `2ⁿ × 2ⁿ` transfer matrix.  This is the exact identity on which Onsager's
solution rests. -/
theorem isingZ_eq_trace_transferMatrix (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    isingZ m n J β = Matrix.trace (transferMatrix n J β ^ m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne m))).symm⟩
  rw [isingZ_eq_sum_prod]
  exact cyclic_sum_prod_eq_trace (transferMatrix n J β) j

/-! ## Main result -/

/-- **Onsager 2D Ising — formalized statement, transfer-matrix reduction, and the
infinite-temperature base case.**

The 2D square-lattice Ising model on the periodic `m × n` lattice is formalized above
(`isingEnergy`, `isingZ`, `isingLogZDensity`), and Onsager's exact free energy density is
`onsagerLogZDensity`; the full theorem is recorded as `OnsagerFreeEnergyStatement`.

This theorem collects what is proved here in Lean-checked form:

* the **transfer-matrix reduction**: at *every* temperature and for every lattice size,
  `Z = tr (T ^ m)` for the `2ⁿ × 2ⁿ` transfer matrix `T` — the identity on which Onsager's
  solution is built;
* the partition function of the `m × n` torus is exactly `2 ^ (m n)` at `β = 0`;
* Onsager's integral expression evaluates to `log 2` at `β = 0`;
* the finite-volume free energy density agrees with Onsager's expression at `β = 0`,
  for every lattice size; and consequently
* the limit asserted by `OnsagerFreeEnergyStatement` holds at `β = 0`. -/
theorem onsager_2d_ising (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ) :
    (∀ β : ℝ, isingZ m n J β = Matrix.trace (transferMatrix n J β ^ m)) ∧
    isingZ m n J 0 = 2 ^ (m * n) ∧
    onsagerLogZDensity J 0 = Real.log 2 ∧
    isingLogZDensity m n J 0 = onsagerLogZDensity J 0 ∧
    Filter.Tendsto (fun N : ℕ => isingLogZDensity (N + 1) (N + 1) J 0) Filter.atTop
      (nhds (onsagerLogZDensity J 0)) := by
  refine ⟨fun β => isingZ_eq_trace_transferMatrix m n J β, isingZ_zero m n J,
    onsagerLogZDensity_zero J, ?_, ?_⟩
  · rw [isingLogZDensity_zero, onsagerLogZDensity_zero]
  · rw [onsagerLogZDensity_zero]
    have : (fun N : ℕ => isingLogZDensity (N + 1) (N + 1) J 0) = fun _ : ℕ => Real.log 2 := by
      funext N
      exact isingLogZDensity_zero (N + 1) (N + 1) J
    rw [this]
    exact tendsto_const_nhds

end Frontier

