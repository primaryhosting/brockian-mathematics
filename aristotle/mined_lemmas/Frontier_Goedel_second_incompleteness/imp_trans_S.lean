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

theorem imp_trans_S {a b c : F.Sent} (h₁ : F.Prov (F.imp a (F.imp b c)))
    (h₂ : F.Prov (F.imp a b)) : F.Prov (F.imp a c) :=
  F.mp (F.mp (F.axS a b c) h₁) h₂

/-- Hypothetical syllogism. -/
