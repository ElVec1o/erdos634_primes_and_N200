import re,sys
from fractions import Fraction as Fr
cur=None; rows=[]
for ln in open('../TRIAGE/inst349.txt').read().splitlines()+open('../TRIAGE/inst_extra.txt').read().splitlines():
    m=re.match(r'== (\d+) (\S+)',ln)
    if m: cur=int(m.group(1)); br=m.group(2); continue
    m=re.match(r'\s+(F[234]) \(e\).*tile \((\d+),(\d+),(\d+)\)(?: \[scale 3k=3\])? N0=(\d+)',ln)
    if m and 'R8' in br:
        rows.append((cur,m.group(1),int(m.group(2)),int(m.group(3)),int(m.group(4)),int(m.group(5))))
def cls(N,F,a,b,c):
    r=Fr(max(a,b),min(a,b))
    if F=='F4': return 'F4a<b' if a<b else ('F4rev' if r<=Fr(7,5) else 'F4rev_open')
    if F=='F3': return 'F3ord' if Fr(a,b)<Fr(2725,1139) else 'F3_open'
    if F=='F2': return 'F2' if r<=Fr(7,5) else 'F2_open'
from collections import defaultdict
best=defaultdict(list)
for N,F,a,b,c,N0 in rows:
    f={'F4':(2*a+b)*(a+b),'F3':3*(a+2*b)*(a+b),'F2':(a+2*b)*(2*a+b)}[F]
    assert f==N==N0,(N,F,a,b,c,f)
    best[N].append((cls(N,F,a,b,c),F,a,b,c))
import json
cov={N:[x for x in v if not x[0].endswith('open')] for N,v in best.items()}
cov={N:v for N,v in cov.items() if v}
from collections import Counter
print(len(best),len(cov),Counter(x[0] for v in cov.values() for x in v[:1]))
json.dump({str(k):v for k,v in cov.items()},open('covered.json','w'))
for N in sorted(cov)[:12]: print(N,cov[N])
