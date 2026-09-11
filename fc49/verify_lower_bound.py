#!/usr/bin/env python3
"""Standalone, integer-only check of the explicit fifteen-block Non-FC example.

Also checks the counting data for an explicitly defined union-closed extension
on 138 points. The enormous extension is specified by slices, not enumerated.
"""
from itertools import combinations
import json
from pathlib import Path

def require(ok,message):
    if not ok:raise RuntimeError(message)

X=(1<<9)-1
core=(1<<7)|(1<<8)
A=sorted({(1<<6)|sum(1<<i for i in t) for t in combinations(range(4),3)}
         |{core|(1<<i)|(1<<j) for i in range(4) for j in [4,5]}
         |{core|(1<<i)|(1<<j) for i,j in combinations([4,5,6],2)})
require(len(A)==15 and all(a.bit_count()==4 for a in A),'Bad generator family')
K=[[a for a in A if (a>>i)&1] for i in range(7)]+[[core|(1<<4),core|(1<<5)]]*2
Bs=[];R=[]
for i,ki in enumerate(K):
    B={s for s in range(512) if not((s>>i)&1) or any((s&k)==k for k in ki)}
    require(all((s|t) in B for s in B for t in B),'Auxiliary not union-closed')
    require(all((s|a) in B for s in B for a in A),'Auxiliary not generator-stable')
    Bs.append(sorted(B))
    R.append([2*sum((s>>j)&1 for s in B)-len(B) for j in range(9)])
lam=[3,3,3,3,13,13,5,35,35]
v=[sum(l*r[i] for l,r in zip(lam,R)) for i in range(9)]
require(v==[-13,-13,-13,-13,-57,-57,-65,-5,-5],'Incorrect dual sum')
C={0}
for a in A:C|={s|a for s in C}
require(len(C)==100 and all((s|t) in C for s in C for t in C),'Invalid generator closure')
require(sorted(s for s in C if s.bit_count()==4)==A,'The closure has unexpected four-sets')
for B in Bs:
    S=set(B)
    require(all((c|b) in S for c in C for b in B),'Closure/auxiliary slice stability failed')
rC=[2*sum((s>>i)&1 for s in C)-len(C) for i in range(9)]
tags=[3,3,3,3,15,15,5,41,41]
imbalance=[rC[i]+sum(t*r[i] for t,r in zip(tags,R)) for i in range(9)]
require(sum(tags)==129 and imbalance==[-5,-5,-5,-5,-31,-31,-55,-49,-49],'Incorrect explicit-extension imbalance')
correction=len(C)+sum(t*len(B) for t,B in zip(tags,Bs))-512*(sum(tags)+1)
require(correction==-21909,'Incorrect cardinality formula')
D=json.loads((Path(__file__).resolve().parent/'data/lower15.json').read_text())
require(D['A']==A and D['basis']==K and D['auxiliaries']==Bs and D['rows']==R and D['multipliers']==lam and D['dual_sum']==v,'Stored certificate mismatch')
E=D['explicit_extension']
require(E['union_closure']==sorted(C) and E['closure_imbalance']==rC and E['tag_class_sizes']==tags and E['total_imbalance']==imbalance and E['outside_points']==129 and E['cardinality_correction']==correction,'Stored extension mismatch')
print('A =',A)
print('Auxiliary sizes =',[len(B) for B in Bs])
print('Rows:');print(*R,sep='\n')
print('Dual multipliers =',lam)
print('Dual sum =',v)
print('Union closure: 100 sets, exactly 15 four-sets.')
print('Explicit extension: 138 points; |F| = 2^138 - 21909.')
print('Original-point imbalances =',imbalance)
print('PASS: FC(4,9) >= 16.')
