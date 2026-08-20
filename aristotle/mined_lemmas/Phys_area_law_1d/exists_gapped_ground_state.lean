import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

lemma exists_gapped_ground_state {N d : ℕ} (c0 : Config N d) :
    ∃ (H : Matrix (Config N d) (Config N d) ℂ) (psi : Config N d → ℂ) (E gap : ℝ),
      IsGroundStateWithGap H psi E gap := by
  classical
  refine ⟨Matrix.diagonal (fun x => if x = c0 then (0 : ℂ) else 1),
    (fun x => if x = c0 then (1 : ℂ) else 0), 0, 1, ?_, ?_, ?_, one_pos, ?_⟩
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    by_cases h : i = c0 <;> simp [h, IsSelfAdjoint]
  · simp [apply_ite norm]
  · funext x
    rw [Matrix.mulVec_diagonal]
    by_cases h : x = c0 <;> simp [h]
  · intro phi hphi
    have hc0 : phi c0 = 0 := by simpa using hphi
    have hterm : ∀ x : Config N d,
        (starRingEnd ℂ) (phi x)
            * (Matrix.diagonal (fun y => if y = c0 then (0 : ℂ) else 1)).mulVec phi x
          = (((‖phi x‖ ^ 2 : ℝ) : ℂ)) := by
      intro x
      rw [Matrix.mulVec_diagonal]
      by_cases h : x = c0
      · simp [h, hc0]
      · rw [if_neg h, one_mul, mul_comm, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq _
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Complex.ofReal_sum, Complex.ofReal_re]
    simp

/-- **Area law for a gapped ground state of a one-dimensional chain.**

This is the physics statement in its usual form: for a gapped local Hamiltonian on a
spin chain, the entanglement entropy of the ground state across any cut is bounded by a
constant independent of the block size and of the chain length.

The spectral gap enters through the hypothesis `hastings`: the analytic heart of
Hastings' theorem is precisely the statement that a spectral gap forces the Schmidt
spectrum across every cut to decay exponentially with constants `C, c` that are uniform
in the chain length and the cut position.  That implication is *assumed* here; what is
proved is that it entails the area law, with the explicit universal constant
`Phys.areaLawBound C c`. -/
