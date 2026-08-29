import Mathlib
/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The abstract mechanism: an anomalous (projective) commutation relation
forces every energy level to be degenerate. -/

/-- **Anomaly ⇒ degeneracy.**  If a Hamiltonian `H` commutes with two injective
symmetries `A` and `B` which fail to commute with each other by a phase `ω ≠ 1`
(`B ∘ A = ω • (A ∘ B)`), then no eigenvector of `H` spans its own eigenspace:
each eigenspace of `H` has dimension at least `2`. -/
theorem anomalous_symmetries_degenerate
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A B : V →ₗ[ℂ] V) (ω : ℂ) (hω : ω ≠ 1)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hHA : H ∘ₗ A = A ∘ₗ H) (hHB : H ∘ₗ B = B ∘ₗ H)
    (hanom : B ∘ₗ A = ω • (A ∘ₗ B))
    (E : ℂ) (hE : Module.End.HasEigenvalue H E) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H E) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hvmem, hv0⟩ := hE.exists_hasEigenvector
  have hHv : H v = E • v := Module.End.mem_eigenspace_iff.mp hvmem
  have hspan : (ℂ ∙ v) ≤ Module.End.eigenspace H E :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hvmem
  have h1 : Module.finrank ℂ (ℂ ∙ v) = 1 := finrank_span_singleton hv0
  have heq : (ℂ ∙ v) = Module.End.eigenspace H E := by
    refine Submodule.eq_of_le_of_finrank_le hspan ?_
    omega
  have hAmem : A v ∈ Module.End.eigenspace H E := by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have := LinearMap.congr_fun hHA v
    simp only [LinearMap.comp_apply] at this
    rw [this, hHv, map_smul]
  have hBmem : B v ∈ Module.End.eigenspace H E := by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have := LinearMap.congr_fun hHB v
    simp only [LinearMap.comp_apply] at this
    rw [this, hHv, map_smul]
  rw [← heq, Submodule.mem_span_singleton] at hAmem hBmem
  obtain ⟨a, ha⟩ := hAmem
  obtain ⟨b, hb⟩ := hBmem
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hv0
    apply hA
    rw [← ha]
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hv0
    apply hB
    rw [← hb]
    simp
  have hkey := LinearMap.congr_fun hanom v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hkey
  rw [← ha, ← hb] at hkey
  rw [map_smul, map_smul, ← hb, ← ha] at hkey
  rw [smul_smul, smul_smul, smul_smul] at hkey
  have hzero : (a * b - ω * b * a) • v = 0 := by
    rw [sub_smul, hkey, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · have h' : a * b * (1 - ω) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ha0 h3
      · exact hb0 h3
    · exact hω (sub_eq_zero.mp h2).symm
  · exact hv0 h

/-! ## A chain of an odd number of spin-1/2 (half-integer spin) sites -/

/-- Spin configurations of a chain of `n` sites, each carrying a spin-1/2. -/
abbrev Config (n : ℕ) := Fin n → Bool

/-- The Hilbert space of the chain: functions on configurations. -/
abbrev ChainSpace (n : ℕ) := Config n → ℂ

/-- Flipping every spin of the chain. -/
def flipEquiv (n : ℕ) : Config n ≃ Config n where
  toFun s := fun j => !(s j)
  invFun s := fun j => !(s j)
  left_inv s := by funext j; simp
  right_inv s := by funext j; simp

/-- Global π-rotation about the `x`-axis, `⊗ⱼ Xⱼ`. -/
noncomputable def rotX (n : ℕ) : ChainSpace n →ₗ[ℂ] ChainSpace n :=
  (LinearEquiv.funCongrLeft ℂ ℂ (flipEquiv n)).toLinearMap

/-- The sign `(-1)^{#{j : sⱼ = ↑}}` attached to a configuration. -/
noncomputable def sgn {n : ℕ} (s : Config n) : ℂ :=
  (-1) ^ (Finset.univ.filter fun j => s j = true).card

/-- Global π-rotation about the `z`-axis, `⊗ⱼ Zⱼ`. -/
noncomputable def rotZ (n : ℕ) : ChainSpace n →ₗ[ℂ] ChainSpace n where
  toFun f := fun s => sgn s * f s
  map_add' f g := by funext s; simp [mul_add]
  map_smul' c f := by funext s; simp; ring

/-- Translation of the chain by one site. -/
noncomputable def transl (n : ℕ) [NeZero n] : ChainSpace n →ₗ[ℂ] ChainSpace n :=
  (LinearEquiv.funCongrLeft ℂ ℂ
    (Equiv.arrowCongr (Equiv.addRight (1 : Fin n)) (Equiv.refl Bool))).toLinearMap

lemma rotX_injective (n : ℕ) : Function.Injective (rotX n) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (flipEquiv n)).injective

lemma sgn_ne_zero {n : ℕ} (s : Config n) : sgn s ≠ 0 :=
  pow_ne_zero _ (by norm_num)

lemma rotX_apply {n : ℕ} (f : ChainSpace n) (s : Config n) :
    rotX n f s = f (fun j => !(s j)) := rfl

lemma rotZ_apply {n : ℕ} (f : ChainSpace n) (s : Config n) :
    rotZ n f s = sgn s * f s := rfl

lemma rotZ_injective (n : ℕ) : Function.Injective (rotZ n) := by
  intro f g h
  funext s
  have := congrFun h s
  rw [rotZ_apply, rotZ_apply] at this
  exact mul_left_cancel₀ (sgn_ne_zero s) this

private lemma neg_one_pow_compl (k m n : ℕ) (h : k + m = n) :
    ((-1 : ℂ)) ^ m = (-1) ^ n * (-1) ^ k := by
  subst h
  have h2 : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨k, by ring⟩
  rw [pow_add]
  linear_combination (-((-1 : ℂ) ^ m)) * h2

/-- Flipping all spins multiplies the `z`-rotation sign by `(-1)^n`. -/
lemma sgn_flip {n : ℕ} (s : Config n) :
    sgn (fun j => !(s j)) = (-1 : ℂ) ^ n * sgn s := by
  classical
  have hset : (Finset.univ.filter fun j => (!(s j)) = true)
      = (Finset.univ.filter fun j => ¬ (s j = true)) := by
    apply Finset.filter_congr
    intro j _
    simp
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun j => s j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  unfold sgn
  rw [hset]
  exact neg_one_pow_compl _ _ _ hcard

/-- On a chain of odd length the two π-rotations anticommute. -/
lemma rotZ_rotX_anticomm {n : ℕ} (hn : Odd n) :
    rotZ n ∘ₗ rotX n = (-1 : ℂ) • (rotX n ∘ₗ rotZ n) := by
  ext f s
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [rotZ_apply, rotX_apply, rotX_apply, rotZ_apply, sgn_flip, hn.neg_one_pow]
  ring

/-! ## Lieb–Schultz–Mattis -/

/-- **Lieb–Schultz–Mattis.**  Consider a chain of an odd number `n` of half-integer
(spin-1/2) sites, with a Hamiltonian `H` that is translation invariant and invariant
under the global spin rotations by `π` about the `x`- and `z`-axes.  Then the system
cannot have a unique gapped ground state: *every* energy level of `H` — in particular
the ground level — is degenerate, its eigenspace having dimension at least `2`.
(Equivalently: the gap above any eigenstate vanishes, so the chain is gapless or
degenerate.)

The translation invariance hypothesis `hHT` is the one demanded by the physical
statement; the proof shows it is not needed once the number of half-integer spins is
odd. -/
theorem lieb_schultz_mattis
    {n : ℕ} [NeZero n] (hn : Odd n) (H : ChainSpace n →ₗ[ℂ] ChainSpace n)
    (hHT : H ∘ₗ transl n = transl n ∘ₗ H)
    (hHX : H ∘ₗ rotX n = rotX n ∘ₗ H)
    (hHZ : H ∘ₗ rotZ n = rotZ n ∘ₗ H)
    (E : ℂ) (hE : Module.End.HasEigenvalue H E) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H E) :=
  anomalous_symmetries_degenerate H (rotX n) (rotZ n) (-1) (by norm_num)
    (rotX_injective n) (rotZ_injective n) hHX hHZ (rotZ_rotX_anticomm hn) E hE

end Phys

