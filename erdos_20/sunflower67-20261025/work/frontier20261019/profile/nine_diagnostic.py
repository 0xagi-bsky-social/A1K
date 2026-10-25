"""Exact finite enumeration diagnostics, not a Lean proof or exclusion certificate."""
import itertools, json

def mask(xs):
    return sum(1 << x for x in xs)

def sunflower(a, b, c):
    return a & b == a & c == b & c

def valid(f):
    return (all(a & b for a,b in itertools.combinations(f,2))
            and all(not sunflower(a,b,c) for a,b,c in itertools.combinations(f,3)))

def vertices(a):
    return [i for i in range(a.bit_length()) if a >> i & 1]

roots={"triangle": [(1,2),(1,3),(2,3)],
       "path_three": [(1,2),(2,3),(3,4)],
       "path_two_plus_edge": [(1,2),(2,3),(4,5)]}
out={}
for name, edges in roots.items():
    star=[mask((0,*e)) for e in edges]
    candidates=[mask(t) for t in itertools.combinations(range(1,7),3)
                if all(mask(t)&mask(e) for e in edges)]
    answers=[]
    tried=0
    for rem in itertools.combinations(candidates,6):
        tried+=1
        f=star+list(rem)
        degrees=[sum(bool(s>>i&1) for s in f) for i in range(7)]
        if max(degrees)>5 or min(degrees)<3:
            continue
        if valid(f):
            answers.append({"family":[vertices(s) for s in f],"degrees":degrees})
    out[name]={"candidate_count":len(candidates),"six_subsets_checked":tried,
               "answer_count":len(answers),"answers":answers}

# Also enumerate the literal labelled nine-member families on Fin 6.
trips=[mask(t) for t in itertools.combinations(range(6),3)]
nine6=[]
for f in itertools.combinations(trips,9):
    if not valid(f):continue
    completions=[vertices(t) for t in trips if t not in f and valid((*f,t))]
    nine6.append({"family":[vertices(t) for t in f],"completions":completions})
out['Fin6']={"nine_member_count":len(nine6),"completion_counts":sorted(set(len(x['completions']) for x in nine6)),
             "first":nine6[0] if nine6 else None}
print(json.dumps(out,indent=2))
