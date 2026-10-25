#!/usr/bin/env python3
"""Exploratory exact trace probe of the other degree-two motif; no closure claim."""
import hashlib
import itertools as it
import json
import time
from pathlib import Path
from check_r15_degree2_degree6 import rejection, triangle_lifts, sunflower

start = time.monotonic()
rows = []
for overlap in range(4):
    d = (4,5,6)
    e = tuple(range(4,4+overlap)) + tuple(range(7,10-overlap))
    used = sorted({3} | set(d) | set(e))
    first = max(used)+1
    for uv in it.combinations(used + list(range(first,first+2)),2):
        new = sorted(set(uv)-set(used))
        if new != list(range(first,first+len(new))):
            continue
        fam = [frozenset(t) for t in ((0,1,2),(1,2,3),(0,)+uv)]
        fam += triangle_lifts(1,d) + triangle_lifts(2,e)
        why = rejection(fam)
        row = {'D':d,'E':e,'uv':uv,'rejection':why}
        if why is None:
            support = sorted(set().union(*fam))
            fresh = max(support)+1
            allowed = []
            for t in it.combinations([v for v in support if v not in (0,1,2)] + list(range(fresh,fresh+3)),3):
                if rejection(fam+[frozenset(t)]) is None:
                    allowed.append(t)
            row['allowed_next'] = allowed
            row['support'] = support
        rows.append(row)
        if time.monotonic()-start>5:
            raise TimeoutError('five-second bounded exploratory probe')
out=Path(__file__).with_name('R15-degree2-without6-probe.json')
result={'schema':'r15-degree2-without6-probe-v1','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'rows':rows,'motifs':len(rows),'surviving_motifs':sum(x['rejection'] is None for x in rows),
        'seconds':time.monotonic()-start,'assurance':'Exploratory necessary traces, not a completed exclusion.'}
with out.open('x') as f: json.dump(result,f,indent=2)
print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
print(json.dumps([{'D':r['D'],'E':r['E'],'uv':r['uv'],'allowed':len(r['allowed_next'])} for r in rows if r['rejection'] is None]))
