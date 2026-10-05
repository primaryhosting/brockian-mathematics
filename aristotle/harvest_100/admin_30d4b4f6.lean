/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module doc comments,
-- so the header above is written as a plain block comment and repeated below.)
import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-!
## The algebraic core of the Lieb–Schultz–Mattis argument

If a Hamiltonian commutes with two symmetries that *anticommute* with each other, then
every energy level is (at least) two-fold degenerate.  This is the finite-volume mechanism
behind the Lieb–Schultz–Mattis theorem: on a half-integer-spin chain of odd length the two
π-rotations about the `x`- and `z`-axes anticommute, so no energy level — in particular no
ground level — can be a simple eigenvalue.
-/

/-- **Degeneracy from anticommuting symmetries.**
Let `A` be an operator on a finite-dimensional complex vector space, and let `S`, `K` be two
operators commuting with `A` such that `S` is an involution, `K` is injective and `S`, `K`
anticommute.  Then every eigenvalue of `A` has an eigenspace of dimension at least `2`. -/
theorem degenerate_of_anticommuting_symmetries
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (A S K : V →ₗ[ℂ] V)
    (hS : S ∘ₗ S = LinearMap.id)
    (hK : Function.Injective K)
    (hAS : A ∘ₗ S = S ∘ₗ A) (hAK : A ∘ₗ K = K ∘ₗ A)
    (hSK : S ∘ₗ K = -(K ∘ₗ S))
    {E : ℂ} {v : V} (hv : v ≠ 0) (hAv : A v = E • v) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace A E) := by
  set W : Submodule ℂ V := Module.End.eigenspace A E with hW
  have memW : ∀ x : V, x ∈ W ↔ A x = E • x := by
    intro x; rw [hW, Module.End.mem_eigenspace_iff]
  -- `S` and `K` preserve the eigenspace
  have hSmem : ∀ x : V, x ∈ W → S x ∈ W := by
    intro x hx
    rw [memW] at hx ⊢
    have : (A ∘ₗ S) x = (S ∘ₗ A) x := by rw [hAS]
    simpa [hx, map_smul] using this
  have hKmem : ∀ x : V, x ∈ W → K x ∈ W := by
    intro x hx
    rw [memW] at hx ⊢
    have : (A ∘ₗ K) x = (K ∘ₗ A) x := by rw [hAK]
    simpa [hx, map_smul] using this
  have hSS : ∀ x : V, S (S x) = x := by
    intro x
    have : (S ∘ₗ S) x = LinearMap.id (R := ℂ) x := by rw [hS]
    simpa using this
  have hanti : ∀ x : V, S (K x) = -K (S x) := by
    intro x
    have : (S ∘ₗ K) x = (-(K ∘ₗ S)) x := by rw [hSK]
    simpa using this
  -- an eigenvector of the involution `S` inside the eigenspace, with eigenvalue `±1`
  obtain ⟨w, hwW, hw0, ε, hε0, hSw⟩ :
      ∃ w : V, w ∈ W ∧ w ≠ 0 ∧ ∃ ε : ℂ, ε ≠ 0 ∧ S w = ε • w := by
    by_cases h : v + S v = 0
    · refine ⟨v, (memW v).2 hAv, hv, -1, by norm_num, ?_⟩
      have : S v = -v := by
        have := h
        linear_combination (norm := module) this
      rw [this]; module
    · refine ⟨v + S v, W.add_mem ((memW v).2 hAv) (hSmem v ((memW v).2 hAv)), h, 1,
        one_ne_zero, ?_⟩
      rw [map_add, hSS]
      module
  have hKw0 : K w ≠ 0 := fun h => hw0 (hK (by simpa using h))
  have hKwW : K w ∈ W := hKmem w hwW
  -- `w` and `K w` are linearly independent
  have hli : LinearIndependent ℂ ![(⟨w, hwW⟩ : W), ⟨K w, hKwW⟩] := by
    apply LinearIndependent.of_comp W.subtype
    have hcomp : (⇑W.subtype) ∘ ![(⟨w, hwW⟩ : W), ⟨K w, hKwW⟩] = ![w, K w] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp, LinearIndependent.pair_iff]
    intro a b hab
    have hSapp : a • (ε • w) + b • (-(ε • K w)) = 0 := by
      have := congrArg S hab
      rw [map_add, map_smul, map_smul, map_zero, hSw, hanti w, hSw] at this
      simpa [smul_smul] using this
    have h1 : ε • (a • w - b • K w) = 0 := by
      linear_combination (norm := module) hSapp
    have h2 : a • w - b • K w = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact absurd h hε0
      · exact h
    have ha : (2 : ℂ) • (a • w) = 0 := by
      linear_combination (norm := module) hab + h2
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 ha with h | h
      · norm_num at h
      · rcases smul_eq_zero.1 h with h | h
        · exact h
        · exact absurd h hw0
    refine ⟨ha0, ?_⟩
    have : b • K w = 0 := by
      rw [ha0] at hab
      simpa using hab
    rcases smul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hKw0
  have := hli.fintype_card_le_finrank
  simpa using this

/-!
## A concrete half-integer-spin (spin-1/2) chain
-/

/-- The Hilbert space of a chain of `L` spin-1/2 sites: functions on the classical
configurations `Fin L → Bool` (each site carries a two-dimensional, i.e. spin-1/2, space). -/
abbrev Chain (L : ℕ) := (Fin L → Bool) → ℂ

/-- The number of up-spins of a configuration. -/
def zWeight {L : ℕ} (s : Fin L → Bool) : ℕ := (univ.filter fun i => s i = true).card

/-- The global spin flip `∏ᵢ σˣᵢ` (the π-rotation about the `x`-axis). -/
def spinFlipX (L : ℕ) : Chain L →ₗ[ℂ] Chain L where
  toFun ψ := fun s => ψ (fun i => !(s i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The global phase `∏ᵢ σᶻᵢ` (the π-rotation about the `z`-axis). -/
def spinPhaseZ (L : ℕ) : Chain L →ₗ[ℂ] Chain L where
  toFun ψ := fun s => (-1 : ℂ) ^ zWeight s * ψ s
  map_add' _ _ := by funext s; simp [mul_add]
  map_smul' c ψ := by funext s; simp [mul_left_comm]

/-- Translation by one site. -/
def translation (L : ℕ) : Chain L →ₗ[ℂ] Chain L where
  toFun ψ := fun s => ψ (s ∘ finRotate L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma spinFlipX_involutive (L : ℕ) : spinFlipX L ∘ₗ spinFlipX L = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext s
  simp [spinFlipX]

lemma spinFlipX_injective (L : ℕ) : Function.Injective (spinFlipX L) := by
  intro ψ φ h
  have : (spinFlipX L) ((spinFlipX L) ψ) = (spinFlipX L) ((spinFlipX L) φ) := by rw [h]
  have hid := spinFlipX_involutive L
  have h1 : (spinFlipX L ∘ₗ spinFlipX L) ψ = (spinFlipX L ∘ₗ spinFlipX L) φ := this
  rw [hid] at h1
  simpa using h1

lemma spinPhaseZ_involutive (L : ℕ) : spinPhaseZ L ∘ₗ spinPhaseZ L = LinearMap.id := by
  ext ψ s
  have : ((-1 : ℂ) ^ zWeight s) * ((-1 : ℂ) ^ zWeight s) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [LinearMap.coe_comp, Function.comp_apply, spinPhaseZ, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_coe, id_eq]
  rw [← mul_assoc, this, one_mul]

lemma zWeight_flip_add {L : ℕ} (s : Fin L → Bool) :
    zWeight (fun i => !(s i)) + zWeight s = L := by
  have h : zWeight (fun i => !(s i)) = (univ.filter fun i => ¬ (s i = true)).card := by
    simp [zWeight]
  rw [h, zWeight, add_comm]
  rw [Finset.card_filter_add_card_filter_not (p := fun i : Fin L => s i = true)]
  simp

lemma neg_one_pow_of_add_odd {a b L : ℕ} (h : a + b = L) (hL : Odd L) :
    (-1 : ℂ) ^ a = -((-1 : ℂ) ^ b) := by
  have h1 : (-1 : ℂ) ^ a * (-1 : ℂ) ^ b = -1 := by
    rw [← pow_add, h, hL.neg_one_pow]
  have h2 : (-1 : ℂ) ^ b * (-1 : ℂ) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc (-1 : ℂ) ^ a = (-1 : ℂ) ^ a * ((-1 : ℂ) ^ b * (-1 : ℂ) ^ b) := by rw [h2]; ring
    _ = ((-1 : ℂ) ^ a * (-1 : ℂ) ^ b) * (-1 : ℂ) ^ b := by ring
    _ = -1 * (-1 : ℂ) ^ b := by rw [h1]
    _ = -((-1 : ℂ) ^ b) := by ring

/-- On a chain of **odd** length the two π-rotations `∏ᵢ σᶻᵢ` and `∏ᵢ σˣᵢ` anticommute.
This is exactly the half-integer-spin obstruction underlying Lieb–Schultz–Mattis. -/
lemma spinPhaseZ_anticomm_spinFlipX {L : ℕ} (hL : Odd L) :
    spinPhaseZ L ∘ₗ spinFlipX L = -(spinFlipX L ∘ₗ spinPhaseZ L) := by
  ext ψ s
  have hflip := neg_one_pow_of_add_odd (zWeight_flip_add s) hL
  simp only [LinearMap.coe_comp, Function.comp_apply, spinPhaseZ, spinFlipX, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.neg_apply, Pi.neg_apply]
  rw [hflip]
  ring

/-!
## Statement of the Lieb–Schultz–Mattis alternative
-/

/-- The ground level `E₀` of `A` is **degenerate**: its eigenspace has dimension at least two. -/
def Degenerate {L : ℕ} (A : Chain L →ₗ[ℂ] Chain L) (E₀ : ℂ) : Prop :=
  2 ≤ Module.finrank ℂ (Module.End.eigenspace A E₀)

/-- The spectrum of `A` is **gapless at scale `ε`** above `E₀`: there is a different (real)
eigenvalue lying within `ε` of `E₀`. -/
def Gapless {L : ℕ} (A : Chain L →ₗ[ℂ] Chain L) (E₀ ε : ℝ) : Prop :=
  ∃ E : ℝ, E ≠ E₀ ∧ Module.End.HasEigenvalue A (E : ℂ) ∧ |E - E₀| < ε

/-- **Lieb–Schultz–Mattis.**
Consider a chain of `L` half-integer-spin (spin-1/2) sites with `L` odd, and a Hamiltonian `A`
that is translation invariant and invariant under the two π-rotations `∏ᵢ σˣᵢ`, `∏ᵢ σᶻᵢ`.
If `E₀` is a ground energy of `A` (a real eigenvalue, minimal among the real eigenvalues), then
for every `ε` the system is gapless at scale `ε` or its ground level is degenerate.

The proof establishes the second alternative: the two π-rotations anticommute on an odd-length
half-integer-spin chain, so every energy level of a symmetric Hamiltonian — in particular the
ground level — is at least two-fold degenerate.  (Consequently the translation-invariance
hypothesis `hTrans` and the minimality hypothesis `hmin`, which are part of the physical setting
requested, are not needed for the conclusion.) -/
theorem lieb_schultz_mattis {L : ℕ} (hL : Odd L)
    (A : Chain L →ₗ[ℂ] Chain L)
    (hTrans : A ∘ₗ translation L = translation L ∘ₗ A)
    (hX : A ∘ₗ spinFlipX L = spinFlipX L ∘ₗ A)
    (hZ : A ∘ₗ spinPhaseZ L = spinPhaseZ L ∘ₗ A)
    (E₀ : ℝ) (v : Chain L) (hv : v ≠ 0) (hgs : A v = (E₀ : ℂ) • v)
    (hmin : ∀ E : ℝ, Module.End.HasEigenvalue A (E : ℂ) → E₀ ≤ E)
    (ε : ℝ) :
    Gapless A E₀ ε ∨ Degenerate A (E₀ : ℂ) := by
  right
  exact degenerate_of_anticommuting_symmetries A (spinPhaseZ L) (spinFlipX L)
    (spinPhaseZ_involutive L) (spinFlipX_injective L) hZ hX
    (spinPhaseZ_anticomm_spinFlipX hL) hv hgs

/-- Non-vacuity check: the hypotheses of `lieb_schultz_mattis` are simultaneously satisfiable
(here by the zero Hamiltonian on a three-site chain). -/
lemma lieb_schultz_mattis_hypotheses_satisfiable :
    ∃ (A : Chain 3 →ₗ[ℂ] Chain 3) (v : Chain 3),
      A ∘ₗ translation 3 = translation 3 ∘ₗ A ∧
      A ∘ₗ spinFlipX 3 = spinFlipX 3 ∘ₗ A ∧
      A ∘ₗ spinPhaseZ 3 = spinPhaseZ 3 ∘ₗ A ∧
      v ≠ 0 ∧ A v = ((0 : ℝ) : ℂ) • v ∧
      ∀ E : ℝ, Module.End.HasEigenvalue A (E : ℂ) → (0 : ℝ) ≤ E := by
  refine ⟨0, fun _ => 1, by simp, by simp, by simp, ?_, by simp, ?_⟩
  · intro h
    have := congrFun h (fun _ => true)
    simp at this
  · intro E hE
    obtain ⟨w, hw, hw0⟩ := hE.exists_hasEigenvector
    have h0 : (0 : Chain 3 →ₗ[ℂ] Chain 3) w = (E : ℂ) • w := Module.End.mem_eigenspace_iff.1 hw
    have hEw : (E : ℂ) • w = 0 := h0.symm.trans (LinearMap.zero_apply w)
    rcases smul_eq_zero.1 hEw with h | h
    · have : E = 0 := by exact_mod_cast h
      simp [this]
    · exact absurd h hw0

end Phys

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

