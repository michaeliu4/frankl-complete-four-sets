#!/usr/bin/env python3
"""Exact standard-library enumeration for the common-pair and local-obstruction results.
No graph-isomorphism library or precomputed atlas is used.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions: run without -O, -OO, or PYTHONOPTIMIZE")

import argparse,itertools,json,math
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent

def read_manifest():
 M=json.loads((ROOT/'manifest.json').read_text());assert len({m['id'] for m in M})==len(M)
 for m in M:
  v=list(map(int,(ROOT/m['input']).read_text().split()));n=v[0]
  assert 1<=n<=9 and len(v)>=n+2
  count=v[n+1];assert len(v)==n+2+count
  assert n==m['n'] and v[1:n+1]==m['w'] and v[n+2:]==m['A']
  assert all(w>=0 for w in m['w']) and sum(m['w'])>0
  assert len(set(m['A']))==len(m['A']) and all(0<=a<(1<<n) and a.bit_count()==4 for a in m['A'])
  assert (ROOT/m['proof']).is_file()
 return M

def pairs(n):return list(itertools.combinations(range(n),2))
def permuted_masks(n):
 E=pairs(n);idx={p:i for i,p in enumerate(E)}
 for p in itertools.permutations(range(n)):
  yield p,[1<<idx[tuple(sorted((p[i],p[j])))] for i,j in E]
def transform(mask,images):
 out=0
 while mask:
  b=mask&-mask;out|=images[b.bit_length()-1];mask-=b
 return out
def complement_of_core(m):
 n=m['n']-2;A=set(m['A']);E=pairs(n)
 assert len(A)==len(m['A']) and all(x.bit_count()==4 and x&3==3 for x in A)
 return sum(1<<i for i,(u,v) in enumerate(E) if 3|(1<<(u+2))|(1<<(v+2)) not in A)
def mask_edges(mask,n):return [list(e) for i,e in enumerate(pairs(n)) if mask>>i&1]
def deletion(mask,v,n=7):
 E=pairs(n);verts=[i for i in range(n) if i!=v];new={x:i for i,x in enumerate(verts)};ix={p:i for i,p in enumerate(pairs(n-1))};r=0
 for i,(a,b) in enumerate(E):
  if mask>>i&1 and a!=v and b!=v:r|=1<<ix[(new[a],new[b])]
 return r,verts

def cover(write):
 M=read_manifest();p6=list(permuted_masks(6));p7=list(permuted_masks(7));local={};global14={}
 for m in M:
  C=complement_of_core(m)
  if m['n']==8:
   for p,im in p6:
    q=transform(C,im);s=q
    while True:
     if s not in local:local[s]={'certificate':m['id'],'permutation':list(p)}
     if s==0:break
     s=(s-1)&q
  elif m['n']==9 and len(m['A'])==14:
   for p,im in p7:global14[transform(C,im)]={'certificate':m['id'],'permutation':list(p)}
 all_graphs={sum(1<<i for i in es) for es in itertools.combinations(range(21),7)}
 assert len(all_graphs)==math.comb(21,7)==116280
 remaining=set(all_graphs);table=[];seen=set();types=Counter();labeled=Counter()
 while remaining:
  C=min(remaining);orbit={transform(C,im) for p,im in p7}
  assert orbit<=all_graphs and not(orbit&seen)
  witness=None
  for v in range(7):
   D,verts=deletion(C,v)
   if D in local:
    witness={'kind':'eight_point','deleted_residual_vertex':v,**local[D]};break
  if witness is None and C in global14:witness={'kind':'nine_point',**global14[C]}
  assert witness is not None,('uncovered common-pair orbit',C,mask_edges(C,7))
  # Check the specific claimed embedding by mapping the ACTUAL four-sets.
  mm=next(x for x in M if x['id']==witness['certificate'])
  residual=[i for i in range(7) if witness['kind']!='eight_point' or i!=witness['deleted_residual_vertex']]
  p=witness['permutation'];pointmap=[0,1]+[residual[p[i]]+2 for i in range(len(p))]
  target={3|(1<<(u+2))|(1<<(v+2)) for i,(u,v) in enumerate(pairs(7)) if not(C>>i&1)}
  mapped={sum(1<<pointmap[i] for i in range(mm['n']) if a>>i&1) for a in mm['A']}
  assert mapped<=target
  weight=[0]*9
  for i,w in enumerate(mm['w']):weight[pointmap[i]]=w
  table.append({'complement_mask':C,'complement_edges':mask_edges(C,7),'generator_masks':sorted(target),'orbit_size':len(orbit),'witness':witness,'certificate_element_map':pointmap,'integer_weights':weight,'weight_sum':sum(weight)})
  seen.update(orbit);remaining-=orbit;types[witness['certificate']]+=1;labeled[witness['certificate']]+=len(orbit)
 assert seen==all_graphs and len(table)==65
 out={'labeled_graphs':len(seen),'orbits':len(table),'orbit_table':table,'orbit_counts_by_certificate':dict(types),'labeled_counts_by_certificate':dict(labeled)}
 if write:(ROOT/'common_pair_cover.json').write_text(json.dumps(out,indent=2))
 else:assert out==json.loads((ROOT/'common_pair_cover.json').read_text())
 print('COMMON PAIR: all 116280 labeled complements, 65 isomorphism orbits, covered exactly.')
 print('Orbit counts:',dict(types))
 return out

def validate_aux(n,A,B):
 X=set(B);assert len(X)==len(B)
 assert all(s|a in X for s in B for a in A)
 assert all(s|t in X for s in B for t in B)
def rows(B,n):return [sum(2*((s>>i)&1)-1 for s in B) for i in range(n)]
def lower13():
 D=json.loads((ROOT/'lower13_on9.json').read_text());n=D['n']
 mask=lambda text:sum(1<<(int(c)-1) for c in text)
 A=[mask(x) for x in D['generators']];R=[]
 for j,base in enumerate(D['coatom_bases']):
  K=[mask(x) for x in base];B=[s for s in range(1<<n) if not(s>>j&1) or any(k&s==k for k in K)]
  validate_aux(n,A,B);assert len(B)==D['family_sizes'][j];r=rows(B,n);assert r==D['coefficient_rows'][j];R.append(r)
 lam=D['dual_multipliers']
 if not isinstance(lam,list) or len(lam)!=len(R):
  raise ValueError('lower13: multiplier count must match auxiliary count')
 if not all(type(k) is int and k>=0 for k in lam):
  raise ValueError('lower13: multipliers must be nonnegative integers')
 v=[sum(k*r[i] for k,r in zip(lam,R)) for i in range(n)]
 assert v==D['dual_sum'] and all(x<0 for x in v)
 assert len(A)==13 and all(a&3==3 for a in A)
 print('LOWER BOUND: thirteen common-pair blocks, exact dual sum',v)

def nonfc():
 for file in ['nonfc_core11_8.json','nonfc_core9_8.json']:
  D=json.loads((ROOT/file).read_text());n=D['n'];A=D['A'];R=[]
  for x in D['extensions']:
   j=x['j'];K=x['K'];B=[s for s in range(1<<n) if not(s>>j&1) or any(k&s==k for k in K)]
   validate_aux(n,A,B);assert len(B)==x['size'];r=rows(B,n);assert r==x['row'];R.append(r)
  lam=D['multipliers']
  if not isinstance(lam,list) or len(lam)!=len(R):
   raise ValueError('nonfc: multiplier count must match auxiliary count')
  if not all(type(k) is int and k>=0 for k in lam):
   raise ValueError('nonfc: multipliers must be nonnegative integers')
  v=[sum(k*r[i] for k,r in zip(lam,R)) for i in range(n)]
  assert all(k>=0 for k in D['multipliers']) and v==D['dual_sum'] and all(x<0 for x in v)
  print(file,'exact dual sum',v)

def obstruction():
 M=read_manifest();F=next(x for x in M if x['id']=='core15_two_triangles')['A'];n=9
 assert len(F)==15
 small=[json.loads((ROOT/f).read_text()) for f in ['nonfc_core11_8.json','nonfc_core9_8.json']]
 records=[]
 for v in range(n):
  X=[i for i in range(n) if i!=v];index={x:i for i,x in enumerate(X)}
  B={sum(1<<index[i] for i in range(n) if a>>i&1) for a in F if not(a>>v&1)}
  if not B:records.append({'deleted':v,'empty':True});continue
  found=None
  # In nonempty restrictions the two common core elements remain points 0,1.
  for D in small:
   for p in itertools.permutations(range(2,8)):
    pp=[0,1]+list(p);image={sum(1<<pp[i] for i in range(8) if a>>i&1) for a in D['A']}
    if image==B:found={'deleted':v,'template_parts':D['parts'],'permutation':pp};break
   if found:break
  assert found is not None,('restriction without NonFC template',v)
  records.append(found)
 # All smaller point supports are contained in one of these eight-point restrictions.
 print('LOCAL OBSTRUCTION: all nine eight-point restrictions are empty or isomorphic to certified Non-FC templates.')
 return records

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--write-cover',action='store_true');a=p.parse_args()
 lower13();nonfc();obstruction();cover(a.write_cover)
 print('These checks concern the common-pair subclass, not an unrestricted upper bound below 20.')
