import Mathlib

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

namespace Frontier

section GaleStewart

variable {A : Type*}

/-- In a two–player game on the move set `A`, the players alternate moves, player I moving at
positions of even length and player II at positions of odd length.  Given strategies `σ` for
player I and `τ` for player II, `nextMove σ τ p` is the move played at the position `p`. -/

def nextMove (σ τ : List A → A) (p : List A) : A :=
  if Even p.length then σ p else τ p

/-- `run σ τ p n` is the position reached after `n` further moves, starting from the position `p`,
when the players follow the strategies `σ` and `τ`. -/
