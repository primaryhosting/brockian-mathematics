import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma schrodinger_deficiency_trivial (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (z : ℂ) (hz : z.im ≠ 0)
    (u : E) (hu : ∀ x : schrodingerDomain b,
      ⟪schrodingerOp b V x, u⟫_ℂ = z * ⟪(x : E), u⟫_ℂ) : u = 0 := by
  have hrepr : ∀ n : ℤ, b.repr u n = ⟪b n, u⟫_ℂ := fun n => b.repr_apply_apply u n
  have hsum : Summable fun n => ‖b.repr u n‖ ^ 2 := summable_repr_sq b u
  have heq : ∀ n : ℤ, (((2 + V n : ℝ)) : ℂ) * b.repr u n - b.repr u (n + 1) - b.repr u (n - 1)
      = z * b.repr u n := by
    intro n
    have h := hu (domBasis b n)
    rw [schrodingerOp_basis, coe_domBasis] at h
    simp only [schrodingerBasisImage, inner_sub_left, inner_smul_left, map_add, map_ofNat,
      Complex.conj_ofReal] at h
    simp only [hrepr]
    push_cast
    linear_combination h
  have hzero := deficiency_solution_eq_zero (fun n => 2 + V n) z hz (fun n => b.repr u n) hsum heq
  have : b.repr u = 0 := by ext n; simpa using hzero n
  simpa using congrArg b.repr.symm this

/-- **Essential self-adjointness of the one-dimensional Schrödinger operator `-Δ + V`
(discrete model) for an arbitrary real potential.**

The named `weakRegularity` hypothesis on the potential has been discharged: the statement is
unconditional, the potential `V : ℤ → ℝ` being an arbitrary real-valued function.  The operator
is defined on the dense domain of finitely supported vectors and is essentially self-adjoint,
i.e. the graph of its adjoint is exactly the closure of its graph (equivalently, its closure is
self-adjoint).  The proof follows Weyl's deficiency argument: symmetry plus the fact that the
deficiency equation `H c = ± i c` has no nonzero `ℓ²` solution (a Wronskian/Green identity
computation, the limit point case). -/
