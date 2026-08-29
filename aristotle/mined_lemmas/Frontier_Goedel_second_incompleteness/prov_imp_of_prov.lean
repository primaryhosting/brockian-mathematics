/-
First-order instantiation of the abstract second incompleteness theorem
proved in `RequestProject.GoedelSecondIncompleteness`.
-/

import Mathlib
import RequestProject.GoedelSecondIncompleteness

set_option autoImplicit false

namespace Frontier

open FirstOrder Language

variable {L : Language} {T : L.Theory}

/-- Modus ponens for entailment of first-order sentences. -/

theorem prov_imp_of_prov {a b : F.Sent} (h : F.Prov b) : F.Prov (F.imp a b) :=
  F.mp (F.axK b a) h

/-- The `S`-rule: from `a → (b → c)` and `a → b` infer `a → c`. -/
