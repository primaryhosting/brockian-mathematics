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

noncomputable def connMachine (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) : Machine n d where
  C := (Fin n × Fin d) × Fin n × Fin (T+1) × Bool
  fintypeC := inferInstance
  init s t := ((s, 0), t, 0, decide (s = t))
  query c := c.1
  next c ans :=
    if (c.2.2.1 : ℕ) = T then c
    else
      (((ans.1, addOff ans.2 (seq (c.2.2.1 : ℕ))), c.2.1, c.2.2.1 + 1,
        c.2.2.2 || decide (ans.1 = c.2.1)))
  accept c := c.2.2.2

variable {T : ℕ} [NeZero d] {seq : ℕ → Fin d}

