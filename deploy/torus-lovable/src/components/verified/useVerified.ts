/**
 * useVerified — resolve a theorem name to its sanitized verification certificate.
 *
 * Honesty contract: this hook only ever returns a record that exists in the
 * public verified registry. If the theorem is not found, it returns `record:
 * null` with `status: "unverified"`. A caller MUST render an unverified/blocked
 * state in that case — never a verified badge. The hook does not, and cannot,
 * fabricate a certificate.
 *
 * Resolution order:
 *   1. GET /api/verified/search?name=<theorem>   (live read API)
 *   2. fallback: fetch the static /verified-registry.json and match by name
 *
 * Self-contained: depends only on React. No external UI or data libraries.
 */

import { useEffect, useMemo, useRef, useState } from "react";

export type Register =
  | "PROVED"
  | "DEFINITION"
  | "CONDITIONAL"
  | "DISCHARGED"
  | "CONJECTURE";

/** A sanitized public certificate record (mirror of the exporter output). */
export interface VerifiedRecord {
  name: string;
  module: string;
  register: Register | string;
  kind: string;
  statement: string;
  conditional_rung: string | null;
  discharged_by: string | null;
  axioms: string[];
  axioms_ok: boolean;
  axle_verdict: string | null;
  env: string | null;
  sorry_free: boolean;
  source: string; // "brockian" | "mathlib" | "physlean" | "unknown"
  verified_by: string | null; // "AXLE" | null (checker)
}

export type VerifiedStatus = "loading" | "verified" | "unverified" | "error";

export interface UseVerifiedResult {
  record: VerifiedRecord | null;
  status: VerifiedStatus;
  error: string | null;
}

// Module-level cache so repeated <VerifiedClaim> instances share lookups.
const _cache = new Map<string, VerifiedRecord | null>();
let _staticIndex: Map<string, VerifiedRecord> | null = null;
let _staticLoad: Promise<Map<string, VerifiedRecord>> | null = null;

const SEARCH_ENDPOINT = "/api/verified/search";
const STATIC_REGISTRY = "/verified-registry.json";

/** Narrow an arbitrary object to a VerifiedRecord (defensive at the boundary). */
function coerceRecord(obj: unknown): VerifiedRecord | null {
  if (!obj || typeof obj !== "object") return null;
  const o = obj as Record<string, unknown>;
  if (typeof o.name !== "string" || typeof o.register !== "string") return null;
  return {
    name: o.name,
    module: typeof o.module === "string" ? o.module : "",
    register: o.register as Register,
    kind: typeof o.kind === "string" ? o.kind : "",
    statement: typeof o.statement === "string" ? o.statement : "",
    conditional_rung:
      typeof o.conditional_rung === "string" ? o.conditional_rung : null,
    discharged_by: typeof o.discharged_by === "string" ? o.discharged_by : null,
    axioms: Array.isArray(o.axioms) ? (o.axioms as string[]) : [],
    axioms_ok: Boolean(o.axioms_ok),
    axle_verdict: typeof o.axle_verdict === "string" ? o.axle_verdict : null,
    env: typeof o.env === "string" ? o.env : null,
    sorry_free: Boolean(o.sorry_free),
    source: typeof o.source === "string" ? o.source : "unknown",
    verified_by: typeof o.verified_by === "string" ? o.verified_by : null,
  };
}

/** Load + index the static fallback registry once. */
async function loadStaticIndex(): Promise<Map<string, VerifiedRecord>> {
  if (_staticIndex) return _staticIndex;
  if (_staticLoad) return _staticLoad;
  _staticLoad = (async () => {
    const res = await fetch(STATIC_REGISTRY, { headers: { Accept: "application/json" } });
    if (!res.ok) throw new Error(`static registry ${res.status}`);
    const doc = (await res.json()) as { theorems?: unknown[] };
    const idx = new Map<string, VerifiedRecord>();
    for (const raw of doc.theorems ?? []) {
      const rec = coerceRecord(raw);
      if (rec) idx.set(rec.name, rec);
    }
    _staticIndex = idx;
    return idx;
  })();
  return _staticLoad;
}

/** Try the live search API; return an exact-name match or null. */
async function fetchFromApi(name: string): Promise<VerifiedRecord | null> {
  const url = `${SEARCH_ENDPOINT}?name=${encodeURIComponent(name)}`;
  const res = await fetch(url, { headers: { Accept: "application/json" } });
  if (!res.ok) throw new Error(`search ${res.status}`);
  const data: unknown = await res.json();

  // Accept several honest shapes: a bare record, {result}, or {results:[...]}.
  let candidates: unknown[] = [];
  if (Array.isArray(data)) candidates = data;
  else if (data && typeof data === "object") {
    const d = data as Record<string, unknown>;
    if (Array.isArray(d.results)) candidates = d.results;
    else if (d.result) candidates = [d.result];
    else if (d.name) candidates = [d];
  }

  for (const c of candidates) {
    const rec = coerceRecord(c);
    if (rec && rec.name === name) return rec; // exact match only
  }
  return null;
}

/** Resolve one theorem name to a record (null = not in registry). */
async function resolve(name: string): Promise<VerifiedRecord | null> {
  if (_cache.has(name)) return _cache.get(name) ?? null;

  let record: VerifiedRecord | null = null;
  try {
    record = await fetchFromApi(name);
  } catch {
    // API unavailable — fall through to static registry.
    record = null;
  }
  if (record === null) {
    try {
      const idx = await loadStaticIndex();
      record = idx.get(name) ?? null;
    } catch {
      // Static fallback also failed; surface as "not found" (honest null).
      record = null;
    }
  }
  _cache.set(name, record);
  return record;
}

/**
 * React hook. Pass a fully-qualified theorem name. Returns the certificate
 * record (or null) plus a status suitable for driving verified vs BLOCKED UI.
 */
export function useVerified(theorem: string | null | undefined): UseVerifiedResult {
  const [record, setRecord] = useState<VerifiedRecord | null>(null);
  const [status, setStatus] = useState<VerifiedStatus>("loading");
  const [error, setError] = useState<string | null>(null);
  const reqId = useRef(0);

  useEffect(() => {
    const name = (theorem ?? "").trim();
    const id = ++reqId.current;

    if (!name) {
      setRecord(null);
      setStatus("unverified");
      setError(null);
      return;
    }

    setStatus("loading");
    setError(null);

    resolve(name)
      .then((rec) => {
        if (reqId.current !== id) return; // stale
        setRecord(rec);
        setStatus(rec ? "verified" : "unverified");
      })
      .catch((e: unknown) => {
        if (reqId.current !== id) return;
        setRecord(null);
        setStatus("error");
        setError(e instanceof Error ? e.message : String(e));
      });
  }, [theorem]);

  return useMemo(
    () => ({ record, status, error }),
    [record, status, error]
  );
}

export default useVerified;
