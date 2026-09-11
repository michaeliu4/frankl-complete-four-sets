#!/usr/bin/env python3
"""Replay an explicit same-cardinality counterexample to lexicographic extremality.

Uses one existing exact positive certificate and nine actual admissible negative
families. No full orbit classification or exact FC(4,9) upper bound is required.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions: run without -O, -OO, or PYTHONOPTIMIZE")

from pathlib import Path
from itertools import combinations, islice
from functools import reduce
import json, shutil, subprocess, tempfile

ROOT=Path(__file__).resolve().parent

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

def main() -> None:
    d=json.loads((ROOT/'witness.json').read_text())
    mask=lambda a:sum(1<<(i-1) for i in a)
    lex=[mask(a) for a in islice(combinations(range(1,10),4),14)]
    require(lex==d['positive_lex14_masks'],'Wrong lexicographic family')
    require(reduce(int.__or__,lex)==511,'Lexicographic support is not all nine points')
    tokens=[int(x) for x in (ROOT/'positive.input').read_text().split()]
    n=tokens[0];w=tokens[1:n+1];count=tokens[n+1];a=tokens[n+2:]
    require(n==d['source_n'] and w==d['source_weights'] and a==d['source_generator_masks'] and len(a)==count,'Positive input mismatch')
    p=d['source_to_lex_embedding_zero_based']
    require(len(p)==n and len(set(p))==n and all(0<=i<9 for i in p),'Bad embedding')
    embedded={sum(1<<p[i] for i in range(n) if s>>i&1) for s in a}
    require(embedded<=set(lex),'The FC subconfiguration is not contained in the lexicographic family')
    compiler=shutil.which('g++')
    require(compiler is not None,'A C++17-capable g++ is required')
    with tempfile.TemporaryDirectory(prefix='fc_lex_') as tmp:
        exe=Path(tmp)/'check'
        subprocess.run([compiler,'-O3','-std=c++17',str(ROOT/'verify_positive.cpp'),'-o',str(exe)],check=True)
        run=subprocess.run([str(exe),'verify',str(ROOT/'positive.tree')],input=(ROOT/'positive.input').read_text(),text=True,capture_output=True,check=True)
        print(run.stdout,end='');print(run.stderr,end='')
        require('status 0 ' in run.stdout,'Positive certificate was not accepted')
    h=d['negative14_masks']
    require(len(h)==len(set(h))==14 and all(0<=s<512 and s.bit_count()==4 for s in h),'Invalid fourteen-block negative family')
    require(reduce(int.__or__,h)==511,'Negative support is not all nine points')
    c=json.loads((ROOT/'negative_auxiliaries.json').read_text());rows=[]
    for family in c['auxiliaries']:
        b=set(family)
        require(len(b)==len(family) and all(0<=s<512 for s in b),'Malformed auxiliary family')
        require(all((s|t) in b for s in b for t in b),'Auxiliary is not union-closed')
        require(all((s|a) in b for s in b for a in h),'Auxiliary is not generator-stable')
        rows.append([2*sum((s>>i)&1 for s in b)-len(b) for i in range(9)])
    lam=c['multipliers']
    require(len(rows)==len(lam) and all(isinstance(x,int) and x>=0 for x in lam),'Bad multipliers')
    sums=[sum(k*r[i] for k,r in zip(lam,rows)) for i in range(9)]
    require(rows==c['expected_rows'] and sums==c['expected_dual_sum'] and all(x<0 for x in sums),'Negative certificate failed')
    print('FC positive lexicographic family:',d['positive_lex14_sets'])
    print('Non-FC fourteen-block family:',d['negative14_sets'])
    print('Negative dual sum:',sums)
    print('PASS: the first 14 lexicographic four-sets on [9] are FC, but another 14-block family on [9] is Non-FC.')
    print('This refutes Conjecture 1 of Pulaj-Wood; no unrestricted sixteen-block upper bound was used.')

if __name__=='__main__':
    main()
