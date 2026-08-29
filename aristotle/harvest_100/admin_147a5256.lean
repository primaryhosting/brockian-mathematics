import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
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

namespace Phys

/-! ## Setup

A quantum system is modelled by a complex vector space `V` (the space of states),
a `ℂ`-linear Hamiltonian `A : V →ₗ[ℂ] V`, and a *time-reversal* operator `T`, which is
**antilinear** (conjugate-linear), i.e. a semilinear map for the ring homomorphism
`starRingEnd ℂ` (complex conjugation).

Half-integer spin is encoded by the relation `T ∘ T = -1`, and time-reversal invariance
of the dynamics by the commutation relation `T ∘ A = A ∘ T`.

Kramers' theorem: every (real) energy level of such a system is at least doubly degenerate.
-/

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An antilinear (conjugate-linear) endomorphism of a complex vector space. -/
abbrev Antilinear (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₛₗ[starRingEnd ℂ] V

/-- For a complex number `c`, the quantity `conj c * c + 1` is never zero: its real part
is `‖c‖ ^ 2 + 1 > 0`. -/
lemma conj_mul_self_add_one_ne_zero (c : ℂ) : (starRingEnd ℂ) c * c + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
  nlinarith [sq_nonneg c.re, sq_nonneg c.im]

/-- **Key step.** If `T` is antilinear with `T ∘ T = -1`, then no nonzero vector `v` can have
`T v` proportional to `v`. Equivalently, if `T v = c • v` for some scalar `c`, then `v = 0`. -/
lemma eq_zero_of_antilinear_smul (T : Antilinear V) (hT : ∀ v : V, T (T v) = -v)
    (v : V) (c : ℂ) (hv : T v = c • v) : v = 0 := by
  have h1 : T (T v) = ((starRingEnd ℂ) c * c) • v := by
    rw [hv, T.map_smulₛₗ, hv, smul_smul]
  have h2 : ((starRingEnd ℂ) c * c) • v = -v := by rw [← h1, hT]
  have h3 : ((starRingEnd ℂ) c * c + 1) • v = 0 := by
    rw [add_smul, one_smul, h2, neg_add_cancel]
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h (conj_mul_self_add_one_ne_zero c)
  · exact h

/-- The time-reversed state `T v` of an eigenvector `v` with **real** eigenvalue `μ` is again
an eigenvector with the same eigenvalue. -/
lemma mem_eigenspace_apply (T : Antilinear V) (A : V →ₗ[ℂ] V)
    (hcomm : ∀ v : V, T (A v) = A (T v)) (μ : ℝ) (v : V)
    (hv : v ∈ Module.End.eigenspace A (μ : ℂ)) :
    T v ∈ Module.End.eigenspace A (μ : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have : T (A v) = ((μ : ℂ)) • T v := by
    rw [hv, T.map_smulₛₗ]
    simp
  rw [hcomm] at this
  exact this

/-- A nonzero eigenvector `v` and its time reverse `T v` are linearly independent
(the *Kramers pair*). -/
lemma linearIndependent_kramers_pair (T : Antilinear V) (hT : ∀ v : V, T (T v) = -v)
    (v : V) (hv : v ≠ 0) : LinearIndependent ℂ ![v, T v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hv
  · exfalso
    have h1 : t • T v = (-s) • v := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
    have h2 : T v = (-s / t) • v := by
      have := congrArg (fun x => t⁻¹ • x) h1
      simpa [smul_smul, inv_mul_cancel₀ ht, div_eq_inv_mul] using this
    exact hv (eq_zero_of_antilinear_smul T hT v (-s / t) h2)

end

/-- **Kramers degeneracy.**

Let `V` be a complex vector space of states, `A : V →ₗ[ℂ] V` a Hamiltonian, and
`T : V →ₛₗ[starRingEnd ℂ] V` an antilinear time-reversal operator satisfying

* `T ∘ T = -1` (half-integer spin), and
* `T ∘ A = A ∘ T` (time-reversal invariance).

Then every real energy level `μ` which actually occurs (i.e. whose eigenspace is nonzero)
has degeneracy at least `2`: the eigenspace has rank at least `2`, spanned in part by a
*Kramers pair* `v`, `T v`. -/
theorem kramers_degeneracy {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₛₗ[starRingEnd ℂ] V) (A : V →ₗ[ℂ] V)
    (hT : ∀ v : V, T (T v) = -v)
    (hcomm : ∀ v : V, T (A v) = A (T v))
    (μ : ℝ) (hne : Module.End.eigenspace A (μ : ℂ) ≠ ⊥) :
    2 ≤ Module.rank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
  obtain ⟨v, hvmem, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hTv : T v ∈ Module.End.eigenspace A (μ : ℂ) :=
    mem_eigenspace_apply T A hcomm μ v hvmem
  -- the Kramers pair, viewed inside the eigenspace
  set W := Module.End.eigenspace A (μ : ℂ)
  have hli : LinearIndependent ℂ
      ![(⟨v, hvmem⟩ : W), (⟨T v, hTv⟩ : W)] := by
    have hbase : LinearIndependent ℂ ![v, T v] :=
      linearIndependent_kramers_pair T hT v hv
    rw [LinearIndependent.pair_iff] at hbase ⊢
    intro s t hst
    apply hbase s t
    have := congrArg (Submodule.subtype W) hst
    simpa using this
  have := hli.cardinal_lift_le_rank
  simpa using this

/-- Finite-dimensional form of Kramers degeneracy: the eigenspace of a real energy level `μ`
of a time-reversal invariant half-integer-spin system has dimension at least `2`. -/
theorem kramers_degeneracy_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (T : V →ₛₗ[starRingEnd ℂ] V) (A : V →ₗ[ℂ] V)
    (hT : ∀ v : V, T (T v) = -v)
    (hcomm : ∀ v : V, T (A v) = A (T v))
    (μ : ℝ) (hne : Module.End.eigenspace A (μ : ℂ) ≠ ⊥) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
  have h := kramers_degeneracy T A hT hcomm μ hne
  rw [← Module.finrank_eq_rank] at h
  exact_mod_cast h

/-! ## Non-vacuity: the spin-1/2 system

The hypotheses of `Phys.kramers_degeneracy` are satisfiable: for a single spin-1/2 particle,
`V = ℂ²` and the time-reversal operator is `T = (i σ_y) ∘ (complex conjugation)`,
i.e. `T (v₀, v₁) = (-conj v₁, conj v₀)`, which indeed squares to `-1`.
-/

/-- Time reversal for a single spin-1/2 degree of freedom, as an antilinear map on `ℂ²`. -/
def spinHalfTimeReversal : (Fin 2 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 2 → ℂ) where
  toFun v := ![-(starRingEnd ℂ) (v 1), (starRingEnd ℂ) (v 0)]
  map_add' u v := by
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma spinHalfTimeReversal_sq (v : Fin 2 → ℂ) :
    spinHalfTimeReversal (spinHalfTimeReversal v) = -v := by
  funext i
  fin_cases i <;> simp [spinHalfTimeReversal]

/-- The hypotheses of Kramers' theorem are satisfiable, and the conclusion is nontrivial:
for the spin-1/2 system with Hamiltonian `A = 1` (energy level `μ = 1`) the assumptions hold
and the level indeed has degeneracy exactly `2`. -/
theorem kramers_nonvacuous :
    ∃ (T : (Fin 2 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 2 → ℂ)) (A : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)),
      (∀ v, T (T v) = -v) ∧ (∀ v, T (A v) = A (T v)) ∧
      Module.End.eigenspace A ((1 : ℝ) : ℂ) ≠ ⊥ ∧
      Module.finrank ℂ (Module.End.eigenspace A ((1 : ℝ) : ℂ)) = 2 := by
  have htop : Module.End.eigenspace (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
      ((1 : ℝ) : ℂ) = ⊤ := by
    ext v
    simp
  refine ⟨spinHalfTimeReversal, LinearMap.id, spinHalfTimeReversal_sq, fun v => rfl, ?_, ?_⟩
  · rw [htop]; exact top_ne_bot
  · rw [htop]; simp

end Phys

