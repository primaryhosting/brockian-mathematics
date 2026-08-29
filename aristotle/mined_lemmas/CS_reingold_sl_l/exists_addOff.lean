import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma exists_addOff {d : ℕ} (i e : Fin d) : ∃ a : Fin d, addOff i a = e := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  refine ⟨⟨(e.1 + d - i.1) % d, Nat.mod_lt _ hd⟩, ?_⟩
  apply Fin.ext
  show (i.1 + (e.1 + d - i.1) % d) % d = e.1
  have h1 : (i.1 + (e.1 + d - i.1) % d) % d = (i.1 + (e.1 + d - i.1)) % d := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod]
    conv_rhs => rw [Nat.add_mod]
  rw [h1, show i.1 + (e.1 + d - i.1) = e.1 + d by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt e.isLt]

variable {n d : ℕ}

/-- **Steering.**  Three exploration steps suffice to traverse any prescribed edge `e` at the
current vertex: the first step is forced, the second one walks back along it, and the third
one takes the edge `e`. -/
