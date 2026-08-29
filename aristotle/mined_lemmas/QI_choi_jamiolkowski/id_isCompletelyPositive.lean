import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators MatrixOrder
open Matrix ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
its `((a, p), (b, q))` entry is the `(p, q)` entry of `Φ` applied to the `(a, b)` block. -/

theorem id_isCompletelyPositive :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  cp_of_hasKraus ⟨Unit, inferInstance, fun _ => 1, by intro X; simp⟩

/-- The transpose map on `n × n` matrices. -/
