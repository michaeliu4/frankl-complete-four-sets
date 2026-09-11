#!/usr/bin/env python3
"""Replay the finite proofs using Python integers and a C++ integer min-cut checker.

No optimization package, Internet access, or floating-point arithmetic is required.
Run: python verify.py --workers 3
"""
from __future__ import annotations
import argparse,json,subprocess,time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parent

def require(ok:bool,message:str)->None:
    if not ok:raise RuntimeError(message)

def command(args:list[str],text:str='')->subprocess.CompletedProcess[str]:
    r=subprocess.run(args,input=text,text=True,capture_output=True,cwd=ROOT)
    require(r.returncode==0,f"Command failed: {args}\n{r.stdout}\n{r.stderr}")
    return r

def verify_negative(d:dict)->None:
    n=d['n'];A=d['A'];Bs=d['auxiliaries'];ls=d['multipliers']
    require(len(Bs)==len(ls) and all(type(l) is int and l>=0 for l in ls),'Invalid multipliers')
    rows=[]
    for B in Bs:
        S=set(B)
        require(len(S)==len(B) and all(type(s) is int and 0<=s<1<<n for s in B),'Invalid auxiliary')
        require(all(s|t in S for s in B for t in B),'Auxiliary not union-closed')
        require(all(s|a in S for s in B for a in A),'Auxiliary not generator-stable')
        rows.append([sum(2*(s>>i&1)-1 for s in B) for i in range(n)])
    v=[sum(l*r[i] for l,r in zip(ls,rows)) for i in range(n)]
    require(all(x<0 for x in v) and v==d['dual_sum'],'Incorrect or nonnegative dual sum')
    if 'rows' in d:require(rows==d['rows'],'Row table mismatch')

def verify_record(path:Path)->dict:
    d=json.loads(path.read_text());n=d['n'];A=d['A']
    require(type(n) is int and 1<=n<=9,'Invalid dimension')
    require(len(set(A))==len(A) and all(type(a) is int and 0<=a<1<<n and a.bit_count()==4 for a in A),'Invalid four-set family')
    if d['status']=='NonFC':
        verify_negative(d);return {'record':str(path.relative_to(ROOT)),'status':'NonFC','dual_sum':d['dual_sum']}
    require(d['status']=='FC','Unknown result in proof data')
    w=d['w'];require(len(w)==n and all(type(x) is int and x>=0 for x in w) and sum(w)>0,'Invalid weights')
    inp=(path.parent/'input.txt').read_text();tokens=list(map(int,inp.split()))
    require(tokens==[n,*w,len(A),*A],'Certificate input differs from declared family/weights')
    r=command([str(ROOT/'bin'/'verify_positive'),'verify',str(path.parent/'proof.tree')],inp)
    return {'record':str(path.relative_to(ROOT)),'status':'FC','integer_replay':r.stdout.strip()}

def read_records(folder:str)->list[dict]:
    return [json.loads(p.read_text()) for p in sorted((ROOT/'data'/folder).glob('*/result.json'))]

def main()->None:
    ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=3);args=ap.parse_args()
    require(args.workers>=1,'workers must be positive');start=time.monotonic();(ROOT/'bin').mkdir(exist_ok=True)
    for name in ['verify_positive','enumerate7','expand7','enumerate8_boundary','augment8']:
        command(['g++','-O3','-std=c++17',str(ROOT/'src'/f'{name}.cpp'),'-o',str(ROOT/'bin'/name)])
    paths=sorted((ROOT/'data'/'seven').glob('*/result.json'))+sorted((ROOT/'data'/'eight').glob('*/result.json'))+[ROOT/'data'/'lower13.json']
    results=[]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for i,d in enumerate(pool.map(verify_record,paths)):
            results.append(d)
            if (i+1)%300==0:print(f'Exact witness replay: {i+1}/{len(paths)}',flush=True)
    seven=read_records('seven');eight=read_records('eight')
    require(len(seven)==653 and len(eight)==1863,'Unexpected record counts')
    prev=[0];generation=[]
    for m in range(1,11):
        r=command([str(ROOT/'bin'/'enumerate7')],'\n'.join(map(str,prev))+'\n')
        actual={int(line.split()[0]):list(map(int,line.split()[1:])) for line in r.stdout.splitlines()}
        layer=[d for d in seven if len(d['A'])==m];declared={int(d['key']):d['A'] for d in layer}
        require(len(declared)==len(layer) and actual==declared,f'Seven-point orbit coverage mismatch at size {m}')
        prev=[int(d['key']) for d in layer if d['status']=='NonFC'];generation.append({'size':m,'counts':r.stderr.strip()})
    require(not prev,'Seven-point generation did not terminate')
    negative7=[d for d in seven if d['status']=='NonFC']
    text=''.join(str(len(d['A']))+' '+' '.join(map(str,d['A']))+'\n' for d in negative7)
    r=command([str(ROOT/'bin'/'expand7'),'data/nonfc7_labeled.bin'],text)
    expected_counts=[1,35,595,6545,52360,302561,276885,24465,1365,210,0]
    lines=r.stdout.splitlines();require(lines[0]=='labeled 665022','Labeled count mismatch')
    require([list(map(int,z.split())) for z in lines[1:]]==[[i,k] for i,k in enumerate(expected_counts)],'Labeled size-count mismatch')
    r11=command([str(ROOT/'bin'/'enumerate8_boundary'),'11'],text)
    actual={f'{line.split()[0]}_{line.split()[1]}':list(map(int,line.split()[2:])) for line in r11.stdout.splitlines()}
    layer11=[d for d in eight if len(d['A'])==11]
    require(actual=={d['key']:d['A'] for d in layer11} and len(actual)==1862,'Eight-point eleven-block coverage mismatch')
    neg11=[d for d in layer11 if d['status']=='NonFC'];require(len(neg11)==3,'Expected three negative eleven-block types')
    text11=''.join('11 '+' '.join(map(str,d['A']))+'\n' for d in neg11)
    r12=command([str(ROOT/'bin'/'augment8')],text11)
    actual12={f'{line.split()[0]}_{line.split()[1]}':list(map(int,line.split()[2:])) for line in r12.stdout.splitlines()}
    layer12=[d for d in eight if len(d['A'])==12]
    require(actual12=={d['key']:d['A'] for d in layer12} and len(layer12)==1 and layer12[0]['status']=='FC','Twelve-block coverage mismatch')
    expected_neg={tuple([201,202,204,209,210,212,225,226,228,232,240]),tuple([15,46,209,210,212,216,225,226,228,232,240]),tuple([202,204,209,210,212,216,225,226,228,232,240])}
    require({tuple(d['A']) for d in neg11}==expected_neg,'The negative types used in PROOF.md do not match data')
    report={'status':'PASS','records':len(paths),'positive':sum(d['status']=='FC' for d in results),'negative':sum(d['status']=='NonFC' for d in results),'seven_generation':generation,'eight11_generation':r11.stderr.strip(),'eight12_generation':r12.stderr.strip(),'seconds':time.monotonic()-start,'witnesses':results}
    (ROOT/'verification_report.json').write_text(json.dumps(report,indent=2))
    print('PASS: all exact witnesses and all orbit-generation comparisons verified.',flush=True)
    print(json.dumps({k:report[k] for k in ['records','positive','negative','seconds']},indent=2),flush=True)
if __name__=='__main__':main()
