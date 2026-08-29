import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file header: Lean 4 requires `import` commands to be the very first
commands of a module, so the required header block is placed immediately after
the single `import Mathlib` line.
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

namespace Phys

/-!
## Setting

We formalise the algebraic (Lieb–Schultz–Mattis / Oshikawa–Yamanaka–Affleck) mechanism
that forbids a non-degenerate energy level in a translation invariant spin chain whose
spin per unit cell is a half-odd-integer.

A finite chain is described by:

* a complex vector space `V` (the Hilbert space of the ring of `L` sites),
* the Hamiltonian `H : V →ₗ[ℂ] V`,
* the (invertible) lattice translation `T`,
* the (invertible) `U(1)` twist operator `U = exp (2πi/L · Σⱼ j Sᶻⱼ)` used in the
  flux-insertion argument,
* the spin per unit cell `spin`, assumed to be a half-odd-integer.

The two physical inputs are:

* `H` commutes with `T` (translation invariance) and with `U` (the twist is built from
  a conserved charge, so it commutes with the Hamiltonian);
* the *LSM commutation relation* `T U = e^{2πi·spin} U T`, i.e. conjugating the twist
  operator by a translation produces the anomalous phase `e^{2πi·spin}`, which equals
  `-1` exactly when the spin per unit cell is a half-odd-integer.

The conclusion is that **no** energy level of `H` is simple: every eigenvalue has at
least a two-dimensional eigenspace.  In particular the ground state is degenerate, so
the chain is gapless or degenerate.
-/

/-- Data of a translation invariant spin chain carrying a half-odd-integer spin per unit
cell, together with the twist operator entering the Lieb–Schultz–Mattis flux argument. -/
structure HalfIntegerSpinChain (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The Hamiltonian. -/
  H : V →ₗ[ℂ] V
  /-- The lattice translation operator (invertible). -/
  T : V ≃ₗ[ℂ] V
  /-- The `U(1)` twist ("flux insertion") operator (invertible). -/
  U : V ≃ₗ[ℂ] V
  /-- The spin per unit cell. -/
  spin : ℚ
  /-- The spin per unit cell is a half-odd-integer. -/
  spin_half_integer : ∃ k : ℤ, spin = (k : ℚ) + 1 / 2
  /-- Translation invariance of the Hamiltonian. -/
  translation_invariant : ∀ v : V, H (T v) = T (H v)
  /-- The twist operator is a symmetry of the Hamiltonian. -/
  symmetry_invariant : ∀ v : V, H (U v) = U (H v)
  /-- The Lieb–Schultz–Mattis commutation relation: translating the twist operator
  produces the phase `e^{2πi·spin}`. -/
  lsm_relation :
    ∀ v : V, T (U v) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (spin : ℂ)) • U (T v)

/-- An eigenvalue `E` of `H` is *degenerate* when its eigenspace contains two linearly
independent vectors. -/
def IsDegenerateEigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H : V →ₗ[ℂ] V) (E : ℂ) : Prop :=
  ∃ v w : V, H v = E • v ∧ H w = E • w ∧ LinearIndependent ℂ ![v, w]

/-- For a half-odd-integer spin `s`, the Lieb–Schultz–Mattis phase `e^{2πi s}` equals `-1`. -/
theorem exp_two_pi_I_half_integer (s : ℚ) (hs : ∃ k : ℤ, s = (k : ℚ) + 1 / 2) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) = -1 := by
  obtain ⟨k, hk⟩ := hs
  subst hk
  have hcast : ((((k : ℚ) + 1 / 2 : ℚ)) : ℂ) = (k : ℂ) + 1 / 2 := by push_cast; ring
  rw [hcast]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1 / 2)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I,
    one_mul]

/-- **Lieb–Schultz–Mattis theorem** (algebraic form).

In a translation invariant chain with a half-odd-integer spin per unit cell, obeying the
LSM commutation relation between the translation `T` and the `U(1)` twist `U`, *every*
energy level is degenerate: given any eigenvector `v ≠ 0` of the Hamiltonian with
eigenvalue `E`, the eigenspace of `E` contains a vector linearly independent from `v`.

Consequently the ground state can never be a unique (non-degenerate) state: the chain is
gapless or degenerate. -/
theorem lieb_schultz_mattis {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : HalfIntegerSpinChain V) (E : ℂ) (v : V) (hv : v ≠ 0) (hE : C.H v = E • v) :
    ∃ w : V, C.H w = E • w ∧ LinearIndependent ℂ ![w, v] := by
  by_contra hcon
  push_neg at hcon
  -- If the level were simple, every eigenvector with eigenvalue `E` is a multiple of `v`.
  have key : ∀ w : V, C.H w = E • w → ∃ a : ℂ, w = a • v := by
    intro w hw
    have hdep := hcon w hw
    rw [linearIndependent_fin2] at hdep
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hdep
    push_neg at hdep
    obtain ⟨a, ha⟩ := hdep hv
    exact ⟨a, ha.symm⟩
  -- `T v` and `U v` are again eigenvectors with eigenvalue `E`.
  have hTv : C.H (C.T v) = E • C.T v := by
    rw [C.translation_invariant, hE, map_smul]
  have hUv : C.H (C.U v) = E • C.U v := by
    rw [C.symmetry_invariant, hE, map_smul]
  obtain ⟨t, ht⟩ := key _ hTv
  obtain ⟨u, hu⟩ := key _ hUv
  -- Both scalars are nonzero since `T` and `U` are invertible.
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hv
    have : C.T v = 0 := by rw [ht, zero_smul]
    have := congrArg C.T.symm this
    simpa using this
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hv
    have : C.U v = 0 := by rw [hu, zero_smul]
    have := congrArg C.U.symm this
    simpa using this
  -- Evaluate the LSM relation on `v`; the anomalous phase is `-1`.
  have hrel := C.lsm_relation v
  rw [exp_two_pi_I_half_integer C.spin C.spin_half_integer, hu, ht, map_smul, map_smul,
    ht, hu] at hrel
  simp only [smul_smul] at hrel
  -- `hrel : (u * t) • v = (-1 * t * u) • v`
  have hsub : (u * t - -1 * (t * u)) • v = 0 := by
    rw [sub_smul, hrel, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · have hut : u * t = 0 := by linear_combination h / 2
    rcases mul_eq_zero.mp hut with h2 | h2
    · exact hu0 h2
    · exact ht0 h2
  · exact hv h

/-- Restatement of `Phys.lieb_schultz_mattis`: every energy level of a half-odd-integer-spin
translation invariant chain is a degenerate eigenvalue. -/
theorem lieb_schultz_mattis_isDegenerate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : HalfIntegerSpinChain V) (E : ℂ) (v : V) (hv : v ≠ 0) (hE : C.H v = E • v) :
    IsDegenerateEigenvalue C.H E := by
  obtain ⟨w, hw, hind⟩ := lieb_schultz_mattis C E v hv hE
  exact ⟨w, v, hw, hE, hind⟩

/-!
## The hypotheses are satisfiable

To make sure the statement above is not vacuous we exhibit a spin-`1/2` example:
`V = Fin 2 → ℂ`, `T` the Pauli `X` (site swap on a two-site ring), `U` the Pauli `Z`
(the `U(1)` twist), and `H = 0`.  These satisfy `T U = - U T`, the LSM relation with
`spin = 1/2`.
-/

/-- The Pauli `X` operator on `Fin 2 → ℂ`, as a linear map. -/
def pauliXMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := fun i => f (Equiv.swap 0 1 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Pauli `Z` operator on `Fin 2 → ℂ`, as a linear map. -/
def pauliZMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := fun i => (if i = 0 then (1 : ℂ) else -1) * f i
  map_add' f g := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c f := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

theorem pauliXMap_involutive : pauliXMap.comp pauliXMap = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext i
  simp [pauliXMap]

theorem pauliZMap_involutive : pauliZMap.comp pauliZMap = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext i
  by_cases h : i = 0 <;> simp [pauliZMap, h]

/-- The Pauli `X` operator as a linear equivalence. -/
def pauliX : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.ofLinear pauliXMap pauliXMap pauliXMap_involutive pauliXMap_involutive

/-- The Pauli `Z` operator as a linear equivalence. -/
def pauliZ : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.ofLinear pauliZMap pauliZMap pauliZMap_involutive pauliZMap_involutive

/-- A concrete spin-`1/2` chain satisfying all the hypotheses of
`Phys.lieb_schultz_mattis`, showing that the theorem is not vacuous. -/
def spinHalfExample : HalfIntegerSpinChain (Fin 2 → ℂ) where
  H := 0
  T := pauliX
  U := pauliZ
  spin := 1 / 2
  spin_half_integer := ⟨0, by norm_num⟩
  translation_invariant v := by simp
  symmetry_invariant v := by simp
  lsm_relation v := by
    have hphase : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℚ) : ℂ)) = -1 :=
      exp_two_pi_I_half_integer (1 / 2) ⟨0, by norm_num⟩
    rw [hphase]
    funext i
    fin_cases i <;>
      simp [pauliX, pauliZ, pauliXMap, pauliZMap, LinearEquiv.ofLinear_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right]

theorem lieb_schultz_mattis_nonvacuous : Nonempty (HalfIntegerSpinChain (Fin 2 → ℂ)) :=
  ⟨spinHalfExample⟩

end Phys

