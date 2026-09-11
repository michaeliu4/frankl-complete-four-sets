#!/usr/bin/env python3
"""Reproduce all included exact checks using Python stdlib and a C++17 compiler."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions: run without -O, -OO, or PYTHONOPTIMIZE")

import json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(root/'verify_combinatorics.py')],check=True)
exe=root/'verify_positive'
subprocess.run(['g++','-O3','-std=c++17',str(root/'verify_positive.cpp'),'-o',str(exe)],check=True)
for m in json.loads((root/'manifest.json').read_text()):
 with (root/m['input']).open() as inp:
  out=subprocess.run([str(exe),'verify',str(root/m['proof'])],stdin=inp,text=True,capture_output=True)
 if out.returncode!=0:
  print(m['id'],out.stdout,out.stderr);raise SystemExit(1)
 print(m['id']+': '+out.stdout.strip(),flush=True)
print('All included common-pair certificates verified.')
