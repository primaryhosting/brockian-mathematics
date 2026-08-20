import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem regex_of_isRegular [Fintype α] {L : Language α} (h : L.IsRegular) : IsRegexLang L := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := h
  rw [DFAPath.accepts_eq_sum M]
  exact IsRegexLang.sum _ _ fun j _ => DFAPath.isRegexLang_pathLang M _ _ _

end CS

import Mathlib
import RequestProject.Antimirov
import RequestProject.KleeneAlgorithm
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


namespace CS

/--
**Kleene's theorem** (over a finite alphabet): a language is described by a regular expression
if and only if it is regular, i.e. accepted by a deterministic finite automaton with finitely
many states (`Language.IsRegular`).
-/
