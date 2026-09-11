#!/usr/bin/env python3
"""Reconstruct exact Morris certificates and compare every field to frozen input."""
import json, runpy
from pathlib import Path
if not __debug__: raise RuntimeError("Run without -O or PYTHONOPTIMIZE")
root=Path(__file__).resolve().parent
result=runpy.run_path(str(root/'reconstruct_morris.py'))
expected=json.loads((root/'morris_exact.json').read_text())
if result['out'] != expected: raise RuntimeError('Reconstructed certificates differ from frozen JSON')
print('PASS: all five exact certificates for n=12,...,16 match frozen data.')
