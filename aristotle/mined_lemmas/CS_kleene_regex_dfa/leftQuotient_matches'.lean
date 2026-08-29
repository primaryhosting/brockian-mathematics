/-
Antimirov partial derivatives: every language matched by a regular expression is regular
(i.e. accepted by a DFA with finitely many states).
-/
import Mathlib

namespace CS

open RegularExpression Language Computability

universe u
variable {α : Type u}

/-! ### Membership lemmas for languages -/


theorem leftQuotient_matches' (P : RegularExpression α) (x : List α) :
    P.matches'.leftQuotient x = unionLang (pds P x) := by
  ext y
  rw [Language.mem_leftQuotient, mem_unionLang, mem_pds_iff]

/-- Every language matched by a regular expression is regular. -/
