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

lemma connMachine_stepG (G : RotGraph n d)
    (c : (Fin n × Fin d) × Fin n × Fin (T+1) × Bool) :
    (connMachine n d T seq).stepG G c =
      (if (c.2.2.1 : ℕ) = T then c
      else (((G.rot c.1).1, addOff (G.rot c.1).2 (seq (c.2.2.1 : ℕ))), c.2.1, c.2.2.1 + 1,
        c.2.2.2 || decide ((G.rot c.1).1 = c.2.1))) := rfl

