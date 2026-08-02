-- verified_declarations — the scalable store for the Mathlib + PhysLean harvest.
--
-- Design spec: docs/superpowers/specs/2026-08-02-mathlib-physlean-harvest-design.md (§4 storage).
--
-- HONESTY (spec §2): every row records BOTH `source` (who authored the math) and
-- `verified_by` (how it earned its register). A harvested Mathlib entry is
-- `source='mathlib', verified_by='mathlib-kernel'` — indexed, kernel-verified UPSTREAM.
-- It is NEVER conflated with a Brockian-original `source='brockian', verified_by='AXLE'`,
-- which we verified through our own independent gate. Counts are ALWAYS split by source;
-- see ingest.py:honesty_report() which refuses to merge them.
--
-- This file is the SQLite-compatible DDL (the local store the Mini ingests).
-- The Supabase/Postgres variant differs only in column types — see the trailing comment.

CREATE TABLE IF NOT EXISTS verified_declarations (
    name                TEXT    PRIMARY KEY,          -- fully-qualified decl name; de-duped (Brockian-original wins)
    source              TEXT    NOT NULL,             -- brockian | mathlib | physlean
    module              TEXT    NOT NULL DEFAULT '',  -- Lean module the decl lives in
    kind                TEXT    NOT NULL,             -- theorem | lemma | def | structure | inductive | ...
    register            TEXT    NOT NULL,             -- PROVED | DEFINITION | UNVERIFIED | CONDITIONAL | ...
    verified_by         TEXT    NOT NULL,             -- AXLE | local-build | mathlib-kernel | physlean-kernel
    axioms              TEXT    NOT NULL DEFAULT '[]',-- JSON array of axiom names (via CollectAxioms)
    sorry_free          INTEGER NOT NULL DEFAULT 1,   -- 0/1 boolean
    nonstandard_axioms  INTEGER NOT NULL DEFAULT 0,   -- 0/1 — axioms escape {propext, Classical.choice, Quot.sound}
    type                TEXT    NOT NULL DEFAULT '',  -- pretty-printed type / statement
    harvested_at        TEXT    NOT NULL DEFAULT '',  -- ISO-8601 timestamp of ingest
    source_rev          TEXT    NOT NULL DEFAULT '',  -- upstream revision (mathlib_rev / physlean_rev / git sha) — idempotency key

    -- register vocabulary guard (mirrors gen_registry.derive_register outputs)
    CHECK (source IN ('brockian', 'mathlib', 'physlean')),
    CHECK (verified_by IN ('AXLE', 'local-build', 'mathlib-kernel', 'physlean-kernel')),
    CHECK (sorry_free IN (0, 1)),
    CHECK (nonstandard_axioms IN (0, 1))
);

-- Indexes for the search API's filter axes (spec §4/§6): by source, by register, by module.
CREATE INDEX IF NOT EXISTS idx_verified_source   ON verified_declarations (source);
CREATE INDEX IF NOT EXISTS idx_verified_register ON verified_declarations (register);
CREATE INDEX IF NOT EXISTS idx_verified_module   ON verified_declarations (module);
-- Composite for the honest "clean PROVED, split by source" headline query.
CREATE INDEX IF NOT EXISTS idx_verified_source_register ON verified_declarations (source, register, nonstandard_axioms);

-- ─────────────────────────────────────────────────────────────────────────────
-- SUPABASE / POSTGRES VARIANT (apply via Lovable query_database on BCC 4de2e97f).
-- Same table, richer types. The honesty model is identical — never merge sources.
--
--   CREATE TABLE IF NOT EXISTS verified_declarations (
--       name                TEXT PRIMARY KEY,
--       source              TEXT NOT NULL CHECK (source IN ('brockian','mathlib','physlean')),
--       module              TEXT NOT NULL DEFAULT '',
--       kind                TEXT NOT NULL,
--       register            TEXT NOT NULL,
--       verified_by         TEXT NOT NULL CHECK (verified_by IN ('AXLE','local-build','mathlib-kernel','physlean-kernel')),
--       axioms              JSONB NOT NULL DEFAULT '[]'::jsonb,
--       sorry_free          BOOLEAN NOT NULL DEFAULT TRUE,
--       nonstandard_axioms  BOOLEAN NOT NULL DEFAULT FALSE,
--       type                TEXT NOT NULL DEFAULT '',
--       harvested_at        TIMESTAMPTZ NOT NULL DEFAULT now(),
--       source_rev          TEXT NOT NULL DEFAULT ''
--   );
--   CREATE INDEX IF NOT EXISTS idx_verified_source   ON verified_declarations (source);
--   CREATE INDEX IF NOT EXISTS idx_verified_register ON verified_declarations (register);
--   CREATE INDEX IF NOT EXISTS idx_verified_module   ON verified_declarations (module);
--   CREATE INDEX IF NOT EXISTS idx_verified_source_register
--       ON verified_declarations (source, register, nonstandard_axioms);
--   -- read-only anon access for the <VerifiedClaim> component (Lovable parity):
--   ALTER TABLE verified_declarations ENABLE ROW LEVEL SECURITY;
--   CREATE POLICY verified_read ON verified_declarations FOR SELECT TO anon USING (true);
--   GRANT SELECT ON verified_declarations TO anon;
-- ─────────────────────────────────────────────────────────────────────────────
