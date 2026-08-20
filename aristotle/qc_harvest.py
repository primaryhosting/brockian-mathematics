import sys, subprocess, os
sys.path.insert(0,"scripts"); import axle_client
proj="aristotle/qc_projects.txt"; log="aristotle/qc_verified.log"
def U(*a): return subprocess.run(["uvx","--from","aristotlelib@latest","aristotle",*a],
                                 capture_output=True,text=True,timeout=140).stdout
seen=set(l.split()[0] for l in open(log)) if os.path.exists(log) else set()
idle=U("list","--status","IDLE","--limit","100")
idle_ids={ln.split()[0] for ln in idle.splitlines() if ln[:1].isalnum() and ln.count('-')>=4}
for line in [l for l in open(proj) if l.strip()]:
    pid,slug=line.split()[0],line.split()[1]
    if pid in seen or pid not in idle_ids: continue
    os.makedirs("/tmp/qcloop",exist_ok=True)
    U("download",pid,"--destination",f"/tmp/qcloop/{slug}.tgz")
    d=f"/tmp/qcloop/{slug}"; os.makedirs(d,exist_ok=True)
    subprocess.run(["tar","xzf",f"/tmp/qcloop/{slug}.tgz","-C",d],capture_output=True)
    lf=next((os.path.join(r,f) for r,_,fs in os.walk(d) for f in fs if f.endswith(".lean")),None)
    if not lf: open(log,"a").write(f"{pid} {slug} NO_LEAN -\n"); print(slug,"NO_LEAN"); continue
    c=open(lf,encoding="utf-8").read()
    nthm=c.count("\ntheorem ")+c.startswith("theorem ")
    if "sorry" in c: open(log,"a").write(f"{pid} {slug} HAS_SORRY {nthm} {lf}\n"); print(slug,"HAS_SORRY"); continue
    r=axle_client.check(c, env="lean-4.32.0", timeout=900)
    st="VERIFIED" if r.verified else "FAILED4322"
    open(log,"a").write(f"{pid} {slug} {st} {nthm} {lf}\n"); print(slug,st,nthm,"thms")
# tally
if os.path.exists(log):
    v=[l for l in open(log) if l.split()[2]=="VERIFIED"]
    tot=sum(int(l.split()[3]) for l in v if len(l.split())>3 and l.split()[3].isdigit())
    print(f"CUMULATIVE VERIFIED: {len(v)} projects, ~{tot} theorems")
