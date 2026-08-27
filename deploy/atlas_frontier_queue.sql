-- atlas_frontier_queue: read mirror of research/frontier_queue.json
-- (truth lives in git; this table is display-only. Spec 2026-08-27.)
create table if not exists atlas_frontier_queue (
  id text primary key,
  statement text not null,
  lean_target jsonb not null default '{}',
  source text not null,
  scores jsonb not null default '{}',
  rank integer not null,
  status text not null,
  assigned_engine text,
  evidence jsonb not null default '{}',
  history jsonb not null default '[]',
  generated_at timestamptz,
  synced_at timestamptz not null default now()
);
alter table atlas_frontier_queue enable row level security;
drop policy if exists "anon read frontier queue" on atlas_frontier_queue;
create policy "anon read frontier queue" on atlas_frontier_queue
  for select to anon using (true);
grant select on atlas_frontier_queue to anon;
