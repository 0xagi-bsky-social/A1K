import itertools,json
blocks=[range(3*i,3*i+3) for i in range(3)]
f27=[frozenset(a+b) for i,j in itertools.combinations(range(3),2) for a in itertools.combinations(blocks[i],2) for b in itertools.combinations(blocks[j],2)]
f54=f27+[frozenset(x+9 for x in r) for r in f27]
def assess(f):
    triples=list(itertools.combinations(f,3))
    cores=[a&b for a,b,c in triples if a&b==a&c==b&c]
    return {'rows':len(f),'distinct_rows':len(set(f)),'sizes':sorted(set(map(len,f))),'intersecting':all(a&b for a,b in itertools.combinations(f,2)),'triple_tests':len(triples),'empty_core_sunflowers':sum(not c for c in cores),'positive_core_sunflowers':sum(bool(c) for c in cores)}
disjoint=[frozenset(range(4*i,4*i+4)) for i in range(81)]
print(json.dumps({'single_construction':assess(f27),'two_disjoint_copies':assess(f54),'positive_core_rival_81_disjoint_rows':assess(disjoint)},indent=2))
