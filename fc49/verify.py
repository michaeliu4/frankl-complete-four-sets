#!/usr/bin/env python3
"""Full integer-only replay of the reconstructed FC(4,9)=16 proof.

Requires Python >=3.10 and g++ with C++17 support. The replay neither imports
SciPy nor accepts optimizer statuses or the supplied historical/audit logs.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
RUN=ROOT/'run'

def require(ok:bool,message:str)->None:
    if not ok:raise RuntimeError(message)

def command(args:list[str|Path],text:str='',cwd:Path=ROOT)->subprocess.CompletedProcess[str]:
    p=subprocess.run([str(x) for x in args],input=text,text=True,capture_output=True,cwd=cwd)
    require(p.returncode==0,f"Command failed: {args}\n{p.stdout}\n{p.stderr}")
    return p

def negative(d:dict)->list[int]:
    n=d['n'];A=d['A'];ls=d['multipliers'];Bs=d['auxiliaries']
    require(len(Bs)==len(ls) and all(type(x)is int and x>=0 for x in ls),'Invalid dual multipliers')
    rows=[]
    for B in Bs:
        S=set(B)
        require(len(S)==len(B) and all(type(s)is int and 0<=s<1<<n for s in B),'Invalid auxiliary family')
        require(all(s|t in S for s in B for t in B),'Auxiliary is not union-closed')
        require(all(s|a in S for s in B for a in A),'Auxiliary is not generator-stable')
        rows.append([sum(2*(s>>i&1)-1 for s in B) for i in range(n)])
    v=[sum(l*r[i] for l,r in zip(ls,rows)) for i in range(n)]
    require(all(x<0 for x in v) and v==d['dual_sum'],'Invalid dual sum')
    if 'rows' in d:require(rows==d['rows'],'Stored rows do not match actual auxiliaries')
    return v

def record(entry:dict)->dict:
    path=ROOT/entry['record'];d=json.loads(path.read_text());n=d['n'];A=d['A']
    require(type(n)is int and 1<=n<=9,'Invalid dimension')
    require(len(A)==len(set(A)) and all(type(a)is int and 0<=a<1<<n and a.bit_count()==4 for a in A),'Invalid generator family')
    require(n==entry['n'] and A==entry['A'] and d['status']==entry['status'] and len(A)==entry['blocks'],'Index/record mismatch')
    if d['status']=='NonFC':
        v=negative(d)
        require(d['multipliers']==entry['dual_multipliers'] and v==entry['dual_sum'],'Dual/index mismatch')
        return {'record':entry['record'],'status':'NonFC','dual_sum':v}
    require(d['status']=='FC','Unresolved record')
    w=d['w']
    require(len(w)==n and all(type(x)is int and 0<=x<=10000 for x in w) and sum(w)>0,'Invalid weights')
    require(w==entry['integer_weights'],'Weights/index mismatch')
    text=(path.parent/'input.txt').read_text()
    require(list(map(int,text.split()))==[n,*w,len(A),*A],'Tree input/record mismatch')
    tree=path.parent/'proof.tree'
    p=command([RUN/'bin/verify_positive','verify',tree],text)
    return {'record':entry['record'],'status':'FC','replay':p.stdout.strip(),
            'tree_sha256':hashlib.sha256(tree.read_bytes()).hexdigest()}

def main()->None:
    require(__debug__, "Do not run verification with -O or PYTHONOPTIMIZE")
    ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=4)
    args=ap.parse_args();require(args.workers>=1,'workers must be positive')
    RUN.mkdir(exist_ok=True);(RUN/'bin').mkdir(exist_ok=True);(RUN/'raw').mkdir(exist_ok=True);(RUN/'data').mkdir(exist_ok=True)
    started=time.monotonic();(RUN/'verification_report.json').write_text('{"status":"RUNNING"}\n')
    index=json.loads((ROOT/'certificate_index.json').read_text())
    require(len(index)==4333 and len({e['record'] for e in index})==4333,'Invalid certificate index')
    foundation_entries=[e for e in index if e['record'].startswith('foundation/')]
    new_entries=[e for e in index if e['record'].startswith('certificates/')]
    require(len(foundation_entries)==2517 and len(new_entries)==1815,'Record count mismatch')
    require({e['record'] for e in new_entries}=={str(p.relative_to(ROOT)) for p in (ROOT/'certificates').glob('*/result.json')},'Unindexed or missing new records')

    print('1. Replaying and regenerating the complete foundation.',flush=True)
    p=command([sys.executable,ROOT/'foundation/verify.py','--workers',str(args.workers)])
    (RUN/'foundation.log').write_text(p.stdout+p.stderr)
    foundation_report=json.loads((ROOT/'foundation/verification_report.json').read_text())
    require(foundation_report['status']=='PASS' and foundation_report['records']==2517,'Foundation did not pass')
    for e in foundation_entries:
        d=json.loads((ROOT/e['record']).read_text())
        require(all(d[k]==e[k] for k in ['n','A','status']) and len(d['A'])==e['blocks'],'Foundation/index mismatch')
        if d['status']=='FC':require(d['w']==e['integer_weights'],'Foundation weight mismatch')
        else:require(d['multipliers']==e['dual_multipliers'] and d['dual_sum']==e['dual_sum'],'Foundation negative mismatch')
    print('Foundation PASS: 2,517 certificates and all orbit-generation comparisons.',flush=True)

    for name in ['verify_positive','audit_layers','audit_enumerate9','enumerate8_boundary']:
        command(['g++','-O3','-std=c++17',ROOT/'src'/f'{name}.cpp','-o',RUN/'bin'/name])
    print('2. Replaying all new positive and negative certificates.',flush=True)
    results=[]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures=[pool.submit(record,e) for e in new_entries]
        for i,f in enumerate(as_completed(futures),1):
            results.append(f.result())
            if i%150==0 or i==len(futures):print(f'New certificates: {i}/{len(futures)}',flush=True)
    require(sum(x['status']=='FC' for x in results)==1750 and sum(x['status']=='NonFC' for x in results)==65,'New classification count mismatch')
    lower=next(e for e in index if e['record']=='data/lower15.json')
    lower_result=record(lower)
    p=command([sys.executable,ROOT/'verify_lower_bound.py'])
    (RUN/'lower_bound.log').write_text(p.stdout+p.stderr)
    print('Lower bound PASS: exact fifteen-block Non-FC witness and explicit extension.',flush=True)

    print('3. Regenerating raw eight-point orbit lists and all hereditary/coverage filters.',flush=True)
    negative7=[json.loads(p.read_text()) for p in (ROOT/'foundation/data/seven').glob('*/result.json') if json.loads(p.read_text())['status']=='NonFC']
    bases7=''.join(str(len(d['A']))+' '+' '.join(map(str,d['A']))+'\n' for d in negative7)
    expected_raw={5:610,6:4085,7:21444,8:63608,9:71548,10:20507}
    for m in range(5,11):
        p=command([RUN/'bin/enumerate8_boundary',str(m)],bases7,cwd=ROOT/'foundation')
        (RUN/'raw'/f'raw{m}.txt').write_text(p.stdout);(RUN/'raw'/f'raw{m}.log').write_text(p.stderr)
        require(len(p.stdout.splitlines())==expected_raw[m],f'Raw orbit count mismatch at {m}')
        print('Raw size',m,':',expected_raw[m],'orbits',flush=True)
    patterns=''.join(e['status']+' '+e['record']+' '+str(len(e['A']))+' '+' '.join(map(str,e['A']))+'\n' for e in new_entries)
    (RUN/'data/indexed_patterns.txt').write_text(patterns)
    p=command([RUN/'bin/audit_layers',RUN/'raw',RUN/'data/indexed_patterns.txt',RUN/'data'])
    (RUN/'boundary_coverage.log').write_text(p.stdout+p.stderr);print(p.stdout,flush=True)
    expected_retained={5:600,6:3474,7:11119,8:12378,9:4837,10:825}
    for m,c in expected_retained.items():
        require(len((RUN/'data'/f'retained{m}.txt').read_text().splitlines())==c,f'Retained count mismatch at {m}')
    # Every boundary representative has already received an actual negative certificate.
    boundary=[e for e in index if e['n']==8 and e['status']=='NonFC' and e['blocks'] in (9,10,11)]
    require({m:sum(e['blocks']==m for e in boundary) for m in (9,10,11)}=={9:52,10:13,11:3},'Boundary count mismatch')
    catalog=''.join(str(len(e['A']))+' '+' '.join(map(str,e['A']))+'\n' for e in boundary)
    require(catalog==(ROOT/'data/catalog8.txt').read_text(),'Printed/verified catalogue mismatch')
    (RUN/'data/catalog8.txt').write_text(catalog)
    print('Boundary PASS: exactly 52, 13, 3 Non-FC types at sizes 9, 10, 11.',flush=True)

    print('4. Independently enumerating all sixteen-block augmentations, with pruning cross-checks.',flush=True)
    summaries={}
    for mode in ['normal','no7','nodegree']:
        args9=[RUN/'bin/audit_enumerate9',ROOT/'foundation/data/nonfc7_labeled.bin',RUN/'data/catalog8.txt']
        if mode!='normal':args9.append(mode)
        p=command(args9);(RUN/f'enumeration16_{mode}.log').write_text(p.stdout+p.stderr)
        require(re.search(r'DONE cases 68 visits \d+ leaves 0 ',p.stdout) is not None,'Final enumeration did not exclude every case')
        summaries[mode]=p.stdout.strip();print(mode+': '+p.stdout.strip(),flush=True)
    report={'status':'PASS','theorem':'FC(4,9)=16','foundation_records':2517,'new_records':1816,
            'positive_records':3954,'negative_records':379,'records':4333,
            'boundary_counts':{'9':52,'10':13,'11':3},'enumeration16':summaries,
            'lower15_dual_sum':lower_result['dual_sum'],'new_certificate_replays':results,
            'seconds':time.monotonic()-started}
    (RUN/'verification_report.json').write_text(json.dumps(report,indent=2))
    print('PASS: FC(4,9)=16. All exact certificates, orbit-coverage steps, and independent final searches verified.',flush=True)
    print(json.dumps({k:v for k,v in report.items() if k!='new_certificate_replays'},indent=2),flush=True)

if __name__=='__main__':main()
