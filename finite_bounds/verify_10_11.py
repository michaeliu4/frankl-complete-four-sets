
if not __debug__:
    raise RuntimeError("Certificate checks require assertions: run without -O, -OO, or PYTHONOPTIMIZE")

import json
from pathlib import Path
root=Path(__file__).resolve().parent
for name in ['nonfc_n10_19blocks.json','nonfc_n11_24blocks.json']:
 d=json.loads((root/name).read_text());n=d['n'];A=d['block_masks'];assert len(A)==len(set(A));assert all(a.bit_count()==4 for a in A)
 assert d['blocks']==[[i+1 for i in range(n) if a>>i&1] for a in A]
 R=[];lam=[]
 for f in d['families']:
  i=f['point']-1;K=f['K_masks'];l=f['multiplier'];
  if type(l) is not int or l<0: raise ValueError('Multipliers must be nonnegative integers')
  # All K contain i: this form is union closed because it is the union of the lower cube and an upset.
  assert all(k>>i&1 for k in K)
  B=[s for s in range(1<<n) if not(s>>i&1) or any(s&k==k for k in K)];S=set(B)
  assert all(s|a in S for s in B for a in A)
  assert all(s|t in S for s in B for t in B)
  R.append([2*sum(s>>j&1 for s in B)-len(B) for j in range(n)]);lam.append(l)
 v=[sum(l*r[j] for l,r in zip(lam,R)) for j in range(n)]
 assert v==d['combination'] and max(v)<0
 print(name,'blocks',len(A),'multipliers',lam,'combination',v)
