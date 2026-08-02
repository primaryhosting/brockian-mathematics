/-
  ExtractEnv.lean — Lean environment-dump extractor for the Mathlib/PhysLean harvest.

  Purpose (spec §3 "Extraction architecture"):
    Walk a *built* Lean environment and emit, per non-internal declaration, one NDJSON
    record for indexing into the verified store. This is an INDEXING tool, not a proof:
    we record what Lean's own kernel already verified upstream. Nothing here re-proves
    Mathlib; it produces the provenance a downstream store needs to set
    `verified_by: mathlib-kernel` (spec §2 honesty model) and to EXCLUDE decls with
    non-standard axioms / `sorry` from the clean PROVED count.

  Per-declaration record (one JSON object per line):
    { "name"              : fully-qualified declaration name
    , "kind"              : one of theorem | def | structure | inductive | axiom
                            (NOTE: `lemma` is pure sugar for `theorem` and is INDISTINGUISHABLE
                             in a built environment — both surface as "theorem"; see caveats)
    , "module"            : the module the decl was declared/imported from
    , "type"              : pretty-printed type (via Meta.ppExpr)
    , "axioms"            : axiom footprint (via Lean.collectAxioms)
    , "sorryFree"         : true iff the axiom footprint does NOT contain `sorryAx`
    , "nonstandardAxioms" : true iff any axiom ∉ {propext, Classical.choice, Quot.sound}
                            (literal spec §2 reading; `sorryAx`, if present, is non-standard) }

  Honesty (spec §2): a downstream decl is PROVED (clean) only if
      sorryFree == true  AND  nonstandardAxioms == false.
  These two booleans give the store everything it needs to enforce that split. If a field
  cannot be extracted for a given decl it is simply omitted from that record (never faked).

  ── WHERE THIS RUNS ─────────────────────────────────────────────────────────────────────
  NOT on the Mac Mini (16 GB) — it cannot build Mathlib (env-blocked; documented thrash).
  Run it on a cache-reachable box (CI runner / cloud) where the olean cache exists, e.g.:

      # from a checkout whose `lake` deps (Mathlib v4.32.0) are built / `lake exe cache get`:
      lake env lean --run scripts/harvest/ExtractEnv.lean > mathlib.ndjson
      # optionally restrict to specific root modules:
      lake env lean --run scripts/harvest/ExtractEnv.lean Mathlib PhysLean > all.ndjson

  With no CLI args it imports `Mathlib`. Extra args are treated as additional root modules
  to import (e.g. `PhysLean`). The Mini ingests the resulting NDJSON via run_extract.py.

  Local elaboration of THIS FILE is checked via AXLE (env lean-4.32.0); the actual harvest
  (running `main`, which imports the full library) happens off-Mini.
-/
import Lean

open Lean

namespace Brockian.Harvest

/-- The three axioms Mathlib treats as standard/foundational. A decl whose footprint is a
    subset of these (and is `sorry`-free) is kernel-clean and eligible for PROVED. -/
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Is `n` one of the three standard axioms? -/
def isStdAxiom (n : Name) : Bool := stdAxioms.contains n

/-- Auto-generated equation lemmas (`foo.eq_1`, `foo.eq_def`, …) — indexing noise. -/
def isEqnLemma (s : String) : Bool :=
  (("eq_".isPrefixOf s) && s.length > 3 && (s.drop 3).all Char.isDigit)
    || s == "eq_def" || s == "eq_unfold" || s == "eq_1" || s == "eq_2"

/-- Heuristic filter for compiler-internal / auto-generated names (spec §3: "skip
    compiler-internal names"). Complements `Name.hasMacroScopes` and the ConstantInfo-kind
    skip of constructors/recursors/quotient primitives. Any numeric name component, any
    component beginning with `_`, and the standard auto-generated suffixes are dropped.
    (A production harvest may swap in Mathlib's `Lean.Name.isBlackListed`; this hand-rolled
    version keeps the tool self-contained.) -/
partial def isInternalName : Name → Bool
  | .anonymous => false
  | .num _ _ => true
  | .str p s =>
      "_".isPrefixOf s
      || "match_".isPrefixOf s
      || "proof_".isPrefixOf s
      || isEqnLemma s
      || s == "rec" || s == "recOn" || s == "casesOn" || s == "brecOn"
      || s == "below" || s == "ibelow" || s == "binductionOn" || s == "brecOnInd"
      || s == "noConfusion" || s == "noConfusionType"
      || s == "injEq" || s == "inj" || s == "sizeOf_spec" || s == "sizeOf_eq"
      || s == "ndrec" || s == "recAux" || s == "casesOn'"
      || isInternalName p

/-- Map a `ConstantInfo` to the spec's `kind` string, or `none` to skip the declaration.
    Constructors / recursors / quotient primitives are auto-generated kernel scaffolding and
    are skipped (they are not indexing targets). `structure` vs `inductive` is disambiguated
    via `Lean.isStructure`. -/
def kindOf (env : Environment) (ci : ConstantInfo) : Option String :=
  match ci with
  | .thmInfo _    => some "theorem"
  | .defnInfo _   => some "def"
  | .opaqueInfo _ => some "def"
  | .axiomInfo _  => some "axiom"
  | .inductInfo _ => some (if isStructure env ci.name then "structure" else "inductive")
  | .ctorInfo _   => none
  | .recInfo _    => none
  | .quotInfo _   => none

/-- The module a declaration lives in (imported module name, or the current main module). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.allImportedModuleNames[idx]?).getD env.mainModule
  | none => env.mainModule

/-- Build the JSON record for a single declaration, or `none` if it is skipped. Runs in
    `CoreM`: `collectAxioms` is a `CoreM` action and the pretty-printer runs via `MetaM`. -/
def recordFor (n : Name) (ci : ConstantInfo) : CoreM (Option Json) := do
  let env ← getEnv
  match kindOf env ci with
  | none => return none
  | some kind =>
    let axs ← collectAxioms n
    let sorryFree : Bool := !(axs.contains ``sorryAx)
    let nonstandard : Bool := axs.any (fun a => !(isStdAxiom a))
    let typeStr : String := (← (Meta.ppExpr ci.type).run').pretty (width := 1000000)
    let modName := moduleOf env n
    let axJson : Array Json := axs.map (fun a => Json.str a.toString)
    return some <| Json.mkObj [
      ("name", Json.str n.toString),
      ("kind", Json.str kind),
      ("module", Json.str modName.toString),
      ("type", Json.str typeStr),
      ("axioms", Json.arr axJson),
      ("sorryFree", Json.bool sorryFree),
      ("nonstandardAxioms", Json.bool nonstandard)
    ]

/-- Core extraction: walk `env.constants`, filter internal names, and return one compact
    JSON line per surviving declaration. This is the AXLE-verifiable pure-of-IO core; `main`
    is only the environment-loading + printing wrapper around it. -/
def extractAll : CoreM (Array String) := do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes || isInternalName n then
      continue
    match ← recordFor n ci with
    | some j => out := out.push j.compress
    | none => pure ()
  return out

/-- IO wrapper: import the requested root modules (default `Mathlib`), run `extractAll`
    over the resulting environment, and print one NDJSON record per line to stdout.

    `unsafe` is REQUIRED: `Lean.enableInitializersExecution` is an unsafe primitive, and it
    is the standard, correct incantation for an env-dump entrypoint that imports a library
    and needs its environment extensions live (same pattern LeanDojo / mathlib4 dumpers use).
    Because it is `unsafe`, AXLE's proof-gate lists it as unverifiable-by-its-gate even though
    it compiles cleanly (`okay: True`); the AXLE-verified guarantee here is over the pure
    `CoreM` core (`extractAll` and everything it calls), which is the extraction logic. -/
unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mods : List Name :=
    if args.isEmpty then [`Mathlib] else args.map String.toName
  let imports : Array Import := (mods.map (fun m => ({ module := m } : Import))).toArray
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports (opts := {}) (trustLevel := 1024)
  let ctx : Core.Context := {
    fileName := "<ExtractEnv>",
    fileMap := FileMap.ofString "",
    maxHeartbeats := 0
  }
  let state : Core.State := { env := env }
  let (lines, _) ← Lean.Core.CoreM.toIO Brockian.Harvest.extractAll ctx state
  for line in lines do
    IO.println line

end Brockian.Harvest
