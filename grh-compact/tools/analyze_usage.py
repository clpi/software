import sys, collections, os
S=sys.argv[1]; src=sys.argv[2]  # usage.tsv, src root
roots=["RH","zeta","ne_half","eq_re","eq_re_prim","criterion","bound","star","data","padic","cubic"]
rows=[]
for ln in open(S):
    p=ln.rstrip("\n").split("\t")
    if len(p)<4+len(roots): continue
    name,mod=p[0],p[1]
    try: a,b=int(p[2]),int(p[3])
    except: a=b=0
    fl=[x=="1" for x in p[4:4+len(roots)]]
    rows.append((name,mod,a,b,fl))
# per module: set of line numbers covered by decls; used by root sets
def lines(r): return set(range(r[2],r[3]+1)) if r[2]>0 else set()
mods=collections.defaultdict(lambda: {"all":set(),"rh":set(),"five":set(),"crit":set(),"bound":set(),"star":set(),"data":set()})
for r in rows:
    L=lines(r); m=mods[r[1]]; fl=r[4]
    m["all"]|=L
    if fl[0]: m["rh"]|=L
    if any(fl[0:5]): m["five"]|=L
    for k,i in (("crit",5),("bound",6),("star",7),("data",8)):
        if fl[i]: m[k]|=L
def area(mod):
    q=mod.split(".")
    return ".".join(q[:3]) if q[0] in("Lib","New") and len(q)>2 else ".".join(q[:2])
tot=collections.Counter(); 
A=collections.defaultdict(collections.Counter)
for mod,m in mods.items():
    ar=area(mod)
    for k in m: A[ar][k]+=len(m[k]); tot[k]+=len(m[k])
# raw file lines
raw=0
for d,_,fs in os.walk(src):
    for f in fs:
        if f.endswith(".lean"): raw+=sum(1 for _ in open(os.path.join(d,f),errors="ignore"))
print("decl-lines total",tot["all"],"raw file lines",raw)
for k in ("rh","five","crit","bound","star","data"): print(k, tot[k], f"{100*tot[k]/tot['all']:.1f}%")
print("unused-by-five decl lines", tot["all"]-tot["five"])
print("rh vs five difference", tot["five"]-tot["rh"])
print("\nAREA  all  rh  five  crit  bound  star  data  unused")
for ar,c in sorted(A.items(), key=lambda x:-x[1]["rh"])[:45]:
    print(f"{ar:45s} {c['all']:6d} {c['rh']:6d} {c['five']:6d} {c['crit']:6d} {c['bound']:6d} {c['star']:6d} {c['data']:6d} {c['all']-c['five']:6d}")
mu=[(mod,len(m["all"])) for mod,m in mods.items() if not m["five"]]
print("\nmodules with ZERO decls used by five theorems:",len(mu),"decl lines",sum(x for _,x in mu))
# names checks
names={r[0]:r for r in rows}
for n in ["IsAdicComplete.henselianRing","HenselianRing.is_henselian"]:
    print(n, "not local (mathlib)")
