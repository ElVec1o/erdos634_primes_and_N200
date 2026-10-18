#!/usr/bin/env python3
"""SQF room: exact four-fact verification (fastverify.py of room R8ROWS) of the decoded Paliy layouts for the
OPEN reversed-row R8 values <= 1e6 whose exact check was never run (N > 120000 cap). Sequential, one process, memcap 3000 MB."""
import sys,os,json,subprocess,time
RR=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,RR)
from run_one import build,target_ok
from rows import tiles_all,write_exact,check,frame
OUT='data/witnesses/r8_exact/'
todo=[(135746,'F4rev',155,144,259),(146982,'F3ord',112,75,163),(156647,'F2',145,119,229),(196251,'F3ord',105,104,181),
      (201122,'F2',155,144,259),(247494,'F3ord',160,87,217),(388847,'F2',231,185,361),(397371,'F3ord',155,144,259),
      (428978,'F4rev',287,240,457),(538346,'F4rev',325,264,511),(624338,'F2',287,240,457),(686945,'F4rev',368,297,577),
      (746327,'F2',301,275,499),(914529,'F4rev',400,377,673)]
res=[]
for N,row,a,b,c in todo:
    t0=time.time(); r=dict(N=N,row=row,tile=(a,b,c))
    try:
        L,T,sides,Nn=build(row,a,b,c)
        ok=check(L,T,(a,b,c),Nn); good=all(ok.values()) and target_ok(T,sides,(a,b,c)) and Nn==N
        r['piece_ok']=good
        if good:
            fn=OUT+'u_%d.exact'%N; tl=tiles_all(L); assert len(tl)==N
            write_exact(fn,tl,"%s %s N=%d Paliy layout decoded in R8ROWS/rows.py; exact check by fastverify.py"%(row,(a,b,c),N))
            tp=' '.join("%s %s"%frame(p) for p in T)
            p=subprocess.run("python3 -I %s/fastverify.py %s %d %d %d %s"%(RR,fn,a,b,c,tp),shell=True,capture_output=True,text=True,timeout=1200)
            r['exact_unit']=(p.returncode==0); r['exact_out']=p.stdout.strip()[:160]; r['target']=tp
            if r['exact_unit']: subprocess.run("gzip -f %s"%fn,shell=True)
            else: os.remove(fn)
    except Exception as e:
        r['status']='FAIL: %s'%repr(e)[:160]
    r['sec']=round(time.time()-t0,1); res.append(r); print(r,flush=True)
    json.dump(res,open(OUT+'results.json','w'),indent=0)
