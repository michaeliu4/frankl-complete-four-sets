
if not __debug__:
    raise RuntimeError("Certificate checks require assertions: run without -O, -OO, or PYTHONOPTIMIZE")

from fractions import Fraction as F
from math import lcm
import json
from pathlib import Path
out=[]
for n,r in [(12,2),(13,2),(14,2),(15,2),(16,3)]:
 A=sorted({(1<<q)|(1<<(q+1))|(1<<(q+2))|(1<<x) for q in range(0,4*r,4) for x in range(q+3,n)} | {(1<<q)|(1<<(q+1))|(1<<(q+3))|(1<<x) for q in range(0,4*r,4) for x in range(q+4,n)})
 R=[]
 for i in range(n):
  K=[a for a in A if a>>i&1]
  # Lower cube + upset(K): union closed, and stable since every generator containing i belongs to K.
  B=[s for s in range(1<<n) if not(s>>i&1) or any(s&a==a for a in K)]
  R.append([2*sum(s>>j&1 for s in B)-len(B) for j in range(n)])
 M=[[F(R[j][i]) for j in range(n)]+[F(-1)] for i in range(n)]
 for j in range(n):
  p=next(i for i in range(j,n) if M[i][j]);M[j],M[p]=M[p],M[j];v=M[j][j];M[j]=[x/v for x in M[j]]
  for i in range(n):
   if i!=j:
    v=M[i][j];M[i]=[a-v*b for a,b in zip(M[i],M[j])]
 w=[row[-1] for row in M];assert min(w)>=0
 den=lcm(*(x.denominator for x in w));lam=[int(x*den) for x in w];v=[sum(lam[i]*R[i][j] for i in range(n)) for j in range(n)];assert max(v)<0
 out.append(dict(n=n,r=r,blocks=A,rows=R,multipliers=lam,combination=v));print(n,r,len(A),'strict negative',v,flush=True)
(Path(__file__).resolve().parent/'morris_exact.regenerated.json').write_text(json.dumps(out,indent=2))
