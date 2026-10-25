#!/usr/bin/env python3
"""Discovery-only P10 + I8, arbitrary-support projection at the 68 target.

No solver runs on import or without the explicit --solve flag.  The default
action prints a finite marker catalogue.  Every model assumes that all P10-side
internal four-sets are absent; the new mu41 exclusions establishing this are an
external premise, not replayed here.  I8-side internals are free by default.

Universal structural statements and the ordinary C5/P5/pool lemmas are imported
premises.  A rounded integer dual only certifies its stated finite relaxation.
This v3 imports the prior mu41/cap18 minimum used degree7 and adds small-core and guarded Z-pool rows. No mu42 or exterior support bound is assumed.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import itertools as it
import json
import pathlib
import time
from functools import lru_cache

import numpy as np
from scipy.sparse import coo_matrix

HERE = pathlib.Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / 'frontier20261020/prior-art68/repository/companion/upstream'
LOCAL43 = SOURCE / 'MU42/scripts/local43.py'
REPOSITORY = SOURCE.parents[1]
CROWDING_SOURCES = {
    'written_arbitrary_support_bridge': REPOSITORY / 'paper/main.tex',
    'cross15_certificate': REPOSITORY / 'companion/terminal/cross15/results/cross16_certificate.json',
    'cross15_checker': REPOSITORY / 'companion/terminal/cross15/src/verify.py',
    'crowding26_certificate': REPOSITORY / 'companion/terminal/crowding/certificates/crowding26.json.gz',
    'crowding26_checker': REPOSITORY / 'companion/terminal/crowding/code/verify.py',
    'prior_foundation_ledger': REPOSITORY.parent / 'FOUNDATION_LEDGER.md',
    'prior_selected_replay_receipt': REPOSITORY.parent / 'replay-selected-20261020/RECEIPT.json',
    'current_prior_delta18_unlock': HERE / 'prior-delta18-unlock.json',
    'prior_minimum7_bridge': REPOSITORY.parent / 'analysis/mu41/mu41-analysis.md',
    'additional_core_rows_bridge': HERE / 'D18-additional-core-rows.md',
    'triangle_path_hub_bridge': HERE / 'D18-Q8-internal-research.md',
}
sys.path.insert(0, str(LOCAL43.parent))
import local43 as L

ROOT = 15
X = 1 << ROOT
Y = (1 << 6) - 1
KINDS = ('P8-i1', 'P8-i2', 'Q8')


def mask(vs):
    return sum(1 << v for v in vs)


def points(s):
    return tuple(v for v in range(s.bit_length()) if s >> v & 1)


def move(s, permutation):
    return mask(permutation[v] for v in points(s))


P10 = tuple(mask(map(int, t)) for t in
            '012 015 023 034 045 124 134 135 235 245'.split())
Q8 = tuple(mask((h, *ab)) for h in (0, 1)
           for ab in it.combinations((2, 3, 4), 2)) + (mask((0, 1, 5)), mask((0, 1, 6)))


@lru_cache(None)
def automorphisms(family, size):
    """The full automorphism group in S_size, not a guessed subgroup."""
    target = set(family)
    return tuple(p for p in it.permutations(range(size))
                 if {move(t, p) for t in family} == target)


@lru_cache(None)
def p8_deletion_types():
    """Reconstruct the two deletion orbits under Aut(P10), including coverage."""
    autos = automorphisms(P10, 6)
    if len(autos) != 60:
        raise ValueError('Canonical P10 automorphism count is not 60')
    all_pairs = {tuple(sorted(ab)) for ab in it.combinations(P10, 2)}
    unseen = set(all_pairs)
    result = {}
    covered = set()
    while unseen:
        rep = min(unseen)
        orbit = {tuple(sorted(move(t, p) for t in rep)) for p in autos}
        if not orbit <= unseen:
            raise ValueError('P10 deletion orbits overlap or leave their domain')
        intersection = (rep[0] & rep[1]).bit_count()
        name = f'P8-i{intersection}'
        if name in result or intersection not in (1, 2):
            raise ValueError('Unexpected P8 deletion orbit')
        result[name] = dict(omitted=rep, deletion_orbit=tuple(sorted(orbit)),
                            link=tuple(t for t in P10 if t not in rep))
        unseen -= orbit
        covered |= orbit
    if covered != all_pairs or set(result) != {'P8-i1', 'P8-i2'}:
        raise ValueError('Incomplete P8 deletion classification')
    return result


def literal_star_kind(component, vertex, support):
    """C5/P5 cuts require the entire literal point-link on all other 5 points."""
    edges = tuple(t ^ (1 << vertex) for t in component if t >> vertex & 1)
    used = 0
    for edge in edges:
        used |= edge
    if len(points(support)) != 6 or used != support ^ (1 << vertex):
        return None, None
    vertices = points(used)
    if any(e.bit_count() != 2 for e in edges) or len(set(edges)) != len(edges):
        return None, None
    reached = {vertices[0]}
    while True:
        bigger = reached | {v for e in edges if any(e >> u & 1 for u in reached)
                            for v in points(e)}
        if bigger == reached:
            break
        reached = bigger
    if reached != set(vertices):
        return None, None
    degrees = sorted(sum(e >> v & 1 for e in edges) for v in vertices)
    if len(edges) == 5 and degrees == [2, 2, 2, 2, 2]:
        return 'C5', None
    if len(edges) == 4 and degrees == [1, 1, 2, 2, 2]:
        covers = [mask(ab) for ab in it.combinations(vertices, 2)
                  if all(mask(ab) & e for e in edges)]
        if len(covers) != 1:
            raise ValueError('A literal P5 should have one two-point cover')
        return 'P5', covers[0]
    return None, None


@lru_cache(None)
def graph_signature(edges):
    """Canonical simple graph on its nonisolated vertices, with no new labels."""
    support = 0
    for edge in edges:
        if edge.bit_count() != 2:
            raise ValueError('A point-link graph has a nonedge')
        support |= edge
    vertices = points(support)
    index = {v: i for i, v in enumerate(vertices)}
    local = tuple(mask(index[v] for v in points(edge)) for edge in edges)
    return (len(vertices), min(tuple(sorted(move(edge, p) for edge in local))
                               for p in it.permutations(range(len(vertices)))))


@lru_cache(None)
def intersecting_point_link_templates(k):
    """Rooted graphs in classified I8/I9/I10; no classification of I7."""
    if k not in (8, 9, 10):
        raise ValueError('No rooted template classification below eight')
    families = list(it.combinations(P10, k))
    if k == 8:
        families.append(Q8)
    signatures = set()
    for family in families:
        support = 0
        for t in family:
            support |= t
        for v in points(support):
            edges = tuple(sorted(t ^ (1 << v) for t in family if t >> v & 1))
            signatures.add(graph_signature(edges))
    return frozenset(signatures)


@lru_cache(None)
def geometry(kind):
    if kind not in KINDS:
        raise ValueError('Unknown I8 kind')
    p8 = p8_deletion_types()
    local_z = Q8 if kind == 'Q8' else p8[kind]['link']
    z_size = 7 if kind == 'Q8' else 6
    core_size = 6 + z_size
    z = mask(range(6, core_size))
    zlink = tuple(t << 6 for t in local_z)
    link = P10 + zlink
    star = tuple(X | t for t in link)
    ya = automorphisms(P10, 6)
    za = automorphisms(local_z, z_size)
    # The canonical exterior marker is fixed.  The root is outside this domain.
    group = tuple(p + tuple(v + 6 for v in q) + (core_size,)
                  for p, q in it.product(ya, za))
    shapes, covers, edges = {}, {}, {}
    for v in range(core_size):
        component, support = (P10, Y) if v < 6 else (zlink, z)
        shapes[v], covers[v] = literal_star_kind(component, v, support)
        edges[v] = tuple(t ^ (1 << v) for t in component if t >> v & 1)
    if any(shapes[v] != 'C5' for v in range(6)):
        raise ValueError('Canonical P10 has an unexpected point-link')
    if kind == 'Q8' and any(shapes[v] is not None for v in range(6, core_size)):
        raise ValueError('Q8 has been incorrectly assigned a C5/P5 cut')
    return dict(kind=kind, z=z, z_size=z_size, core_size=core_size,
                exterior=core_size, link=link, star=star, group=group,
                y_aut_order=len(ya), z_aut_order=len(za), shapes=shapes,
                covers=covers, edges=edges,
                graph_signatures={v: graph_signature(tuple(sorted(edges[v]))) for v in edges},
                omitted=() if kind == 'Q8' else p8[kind]['omitted'],
                deletion_orbit=() if kind == 'Q8' else p8[kind]['deletion_orbit'])


@lru_cache(None)
def marker_catalogue(kind):
    g = geometry(kind)
    c, z = g['core_size'], g['z']
    all4 = {mask(vs) for vs in it.combinations(range(c), 4)}
    yinternal = {s for s in all4 if s & Y == s}
    zinternal = {s for s in all4 if s & z == s}
    mixed4 = all4 - yinternal - zinternal
    mixed3 = {mask(vs) | (1 << c) for vs in it.combinations(range(c), 3)
              if mask(vs) & Y and mask(vs) & z}
    domains = (('I', 'internal-Z', zinternal), ('E4_', 'mixed-four-core', mixed4),
               ('E3_', 'mixed-three-core-plus-exterior', mixed3))
    records = {'none': dict(marker=None, category='unmarked', orbit=[])}
    total = set()
    for prefix, category, domain in domains:
        unseen, covered = set(domain), set()
        counter = 0
        while unseen:
            representative = min(unseen)
            orbit = {move(representative, p) for p in g['group']}
            if not orbit <= unseen:
                raise ValueError('Marker orbit overlaps or leaves its domain')
            name = f'{prefix}{counter:02d}'
            records[name] = dict(marker=representative, category=category,
                                 orbit=sorted(orbit))
            unseen -= orbit
            covered |= orbit
            counter += 1
        if covered != domain or total & covered:
            raise ValueError('Incomplete or overlapping marker catalogue')
        total |= covered
    if total != (all4 - yinternal) | mixed3:
        raise ValueError('Marker catalogue misses a requested trace')
    return records


def catalogue_metadata(kind):
    g = geometry(kind)
    records = marker_catalogue(kind)
    return dict(kind=kind, root=ROOT, Y=list(range(6)),
                Z=list(range(6, g['core_size'])), exterior_marker=g['exterior'],
                link=list(g['link']), omitted_local_p10_blocks=list(g['omitted']),
                p8_deletion_orbit=[list(p) for p in g['deletion_orbit']],
                automorphism_orders=dict(Y=g['y_aut_order'], Z=g['z_aut_order'],
                                         product=len(g['group'])),
                literal_point_link_shapes=g['shapes'],
                excluded_Y_internal_count=15,
                records={name: dict(marker=r['marker'], category=r['category'],
                                    orbit_size=len(r['orbit']), orbit=r['orbit'])
                         for name, r in records.items()})


@lru_cache(None)
def local_catalog(kind, T, crowding_imports=True):
    """Seven exact central-anchor coordinates and degree/geometry metadata."""
    g = geometry(kind)
    pts = points(T)
    A = T | X
    px = tuple(sum(B & A == X | (1 << v) for B in g['star']) for v in pts)
    tf = tuple(sum(B & A == A ^ (1 << v) for B in g['star']) for v in pts)
    sx = sum(B & A == X for B in g['star'])
    rows, degrees, near, internal_cost, removable_cost, cover_cost, pool_lower = ([] for _ in range(7))
    for q in it.product(range(4), repeat=3):
        p = px + q
        for e in range(2):
            t = (e,) + tf
            k = tuple(1 + sum(p[j] for j in L.INC[i]) + sum(t) - t[i] for i in range(4))
            if sx + k[0] != 18:
                raise ValueError('Root link is not complete degree 18')
            if sx not in L.local_s_candidates(0, p, t, 17, 0, 0):
                continue
            candidates = [tuple(s for s in L.local_s_candidates(i, p, t, 17, 0, 0)
                                if s + k[i] <= 18) for i in (1, 2, 3)]
            for tail in it.product(*candidates):
                s = (sx,) + tail
                d = tuple(a + b for a, b in zip(s, k))
                if min(d) < 7:
                    continue
                if 1 + sum(p) + sum(t) + sum(s) < 41:
                    continue
                if any(d[i] + d[j] < 19 for i, j in L.PAIRS):
                    continue
                if sum(p) + sum(t) > (12, 14, 17, 19, 22)[sum(a < 8 for a in s)]:
                    continue
                if not L.equality_consistent(p, t, s, k):
                    continue
                if crowding_imports and sum(sorted(s)[-3:]) > 26:
                    continue
                good = True
                ic, rc, gc, lower = [], [], [], []
                for j, v in enumerate(pts, 1):
                    shape = g['shapes'][v]
                    # Every triple through x belongs to the near family. Its
                    # COMPLETE rooted graph must occur in the classified I_k
                    # whenever K is intersecting and k>=8.  No full-support
                    # assumption is needed.  The k=7 case is left unrestricted.
                    if (k[j] in (8, 9, 10) and (s[j] >= 8 or d[j] >= 17)
                            and g['graph_signatures'][v] not in intersecting_point_link_templates(k[j])):
                        good = False
                        break
                    # The empty P10 internal premise is applied only on Y.
                    if v < 6 and (d[j] > 15 or (s[j] >= 8 and k[j] > 5)):
                        good = False
                        break
                    # A separated P5 near component cannot be P10: x has
                    # exactly four incident triples, not five.
                    if shape == 'P5' and d[j] >= 17 and (s[j], k[j]) not in {
                        17: ((10, 7), (9, 8), (8, 9)),
                        18: ((10, 8), (9, 9)),
                    }[d[j]]:
                        good = False
                        break
                    need_i = need_r = need_g = 0
                    if shape == 'C5':
                        need_g = max(0, d[j] - 15,
                                     k[j] - 5 if s[j] >= 8 or d[j] >= 16 else 0)
                    elif shape == 'P5':
                        need_r = max(0, d[j] - 16,
                                     k[j] - 6 if s[j] >= 8 or d[j] >= 17 else 0)
                        need_i = max({17: 1, 18: 4}.get(d[j], 0),
                                     k[j] - 4 if s[j] >= 8 and k[j] >= 8 else 0)
                    ell = 0
                    if shape in ('C5', 'P5'):
                        equal = ((shape == 'C5' and d[j] >= 16) or d[j] >= 17
                                 or (s[j] >= 8 and k[j] >= 8))
                        ell = s[j] if equal else {8: 6, 9: 9, 10: 10}.get(s[j], 0)
                    ic.append(need_i)
                    rc.append(need_r)
                    gc.append(need_g)
                    lower.append(ell)
                if not good:
                    continue
                if any(lower[a] + lower[b] > (15 if crowding_imports else 16)
                       for a, b in it.combinations(range(3), 2)
                       if pts[a] < 6 and pts[b] < 6):
                    continue
                rows.append(q + (e,) + tail)
                degrees.append(d[1:])
                near.append(k[1:])
                internal_cost.append(ic)
                removable_cost.append(rc)
                cover_cost.append(gc)
                pool_lower.append(lower)
    def array(values, width):
        return np.asarray(values, dtype=np.int16).reshape((-1, width))
    return dict(rows=array(rows, 7), degrees=array(degrees, 3), near=array(near, 3),
                internal=array(internal_cost, 3), removable=array(removable_cost, 3),
                covers=array(cover_cost, 3), pool_lower=array(pool_lower, 3))


def build(kind, case='none', empty_z=False, assigned_z=None, forbidden=(),
          forbid_four_core=False, degree_distributions=False, crowding_imports=True):
    """Return traces,bounds,A,b,E,f,upper_labels,local_catalogue_sizes.

    Optional exclusions and a complete assigned-Z pattern are additional branch
    premises.  With assigned_z=None all Z-internal four-sets remain free.
    """
    if not crowding_imports:
        raise ValueError('v3 requires the explicitly imported prior crowding/minimum7/cross15 package')
    g = geometry(kind)
    record = marker_catalogue(kind)[case]
    marker = record['marker']
    core_size, z = g['core_size'], g['z']
    n = core_size + int(marker is not None and bool(marker >> core_size))
    traces = tuple(mask(vs) for k in range(5) for vs in it.combinations(range(n), k))
    index = {s: i for i, s in enumerate(traces)}
    N = len(traces)
    lo = np.zeros(N, dtype=np.int64)
    hi = np.asarray([{0: 27, 1: 18, 2: 6, 3: 2, 4: 1}[s.bit_count()]
                     for s in traces], dtype=np.int64)
    selected = [] if marker is None else [marker]
    if assigned_z is not None:
        assigned_z = tuple(assigned_z)
        if len(set(assigned_z)) != len(assigned_z) or any(
                s not in index or s.bit_count() != 4 or s & z != s for s in assigned_z):
            raise ValueError('Assigned Z pattern must be distinct internal four-sets')
        if empty_z and assigned_z:
            raise ValueError('Nonempty assigned Z pattern conflicts with empty_z')
        selected.extend(assigned_z)
    forbidden = tuple(forbidden)
    if any(s not in index for s in forbidden):
        raise ValueError('A forbidden trace lies outside this actual-point universe')
    for i, s in enumerate(traces):
        if s.bit_count() == 4:
            if s & Y == s or (empty_z and s & z == s):
                hi[i] = 0
            if assigned_z is not None and s & z == s:
                lo[i] = hi[i] = int(s in assigned_z)
            if forbid_four_core and s < (1 << core_size):
                hi[i] = 0
        if s in forbidden:
            hi[i] = 0
    selected = tuple(dict.fromkeys(selected))
    fixed = g['star'] + selected
    if any(A & B == A & C == B & C for A, B, C in it.combinations(fixed, 3)):
        raise ValueError('Selected actual members already form a sunflower')
    for M in selected:
        lo[index[M]] = 1
    # Both fixed members lie inside the represented universe (with x appended),
    # so these are exact actual intersections, even for proper residual traces.
    relevant_pairs = [(A, B) for A, B in it.combinations(fixed, 2)
                      if not (A & X and B & X)]
    for i, s in enumerate(traces):
        if any(s & A == s & B == A & B for A, B in relevant_pairs):
            hi[i] = 0
    if np.any(lo > hi):
        raise ValueError('Conflicting selected and forbidden traces')
    bounds = [(int(l), int(u)) for l, u in zip(lo, hi)]
    upper, equal, labels = [], [], []

    def put(label, terms, rhs):
        upper.append(({i: int(w) for i, w in terms.items() if w}, int(rhs)))
        labels.append(label)

    def eq(terms, rhs):
        equal.append(({i: int(w) for i, w in terms.items() if w}, int(rhs)))

    incidence = {v: [i for i, s in enumerate(traces) if s >> v & 1] for v in range(n)}
    fixed_degree = {v: sum(T >> v & 1 for T in g['link']) for v in range(n)}
    for k, cap in ((1, 18), (2, 6), (3, 2)):
        for vs in it.combinations(range(n), k):
            u = mask(vs)
            put(('incidence', u), {i: 1 for i, s in enumerate(traces) if s & u == u},
                cap - sum(T & u == u for T in g['link']))
    for v in range(n):
        put(('prior-minimum-used-degree7', v), dict.fromkeys(incidence[v], -1),
            fixed_degree[v] - 7)
    core_mask = Y | z
    put(('small-complete-core-intersecting-H27',),
        {i: 1 for i, s in enumerate(traces) if (s & core_mask).bit_count() <= 2}, 27)
    zpools = {v: [i for i, s in enumerate(traces) if s & z == 1 << v] for v in points(z)}
    zedges = {frozenset((u, v)) for u, v in it.combinations(points(z), 2)
              if any(not (B & ~(z | X)) and not (B & ((1 << u) | (1 << v))) for B in fixed)}
    for v, ids in zpools.items():
        put(('Z-singleton-cap10', v), dict.fromkeys(ids, 1), 10)
    for edge in sorted(zedges, key=lambda e: tuple(sorted(e))):
        u, v = sorted(edge)
        put(('guarded-Z-imported-cross15', u, v), dict.fromkeys(zpools[u] + zpools[v], 1), 15)
    zcliques = [tuple(vs) for size in range(1, g['z_size'] + 1)
                for vs in it.combinations(points(z), size)
                if all(frozenset(pair) in zedges for pair in it.combinations(vs, 2))]
    maximal = [vs for vs in zcliques if not any(set(vs) < set(ws) for ws in zcliques)]
    for vs in maximal:
        put(('guarded-Z-clique-H27', vs), {i: 1 for v in vs for i in zpools[v]}, 27)
    for A in fixed:
        put(('disjoint-H27', A), {i: 1 for i, s in enumerate(traces) if not s & A},
            27 - sum(not B & A for B in g['star']))
        put(('actual-anchor-mu41', A), {i: -1 for i, s in enumerate(traces) if s & A},
            sum(bool(B & A) for B in g['star']) - 41)
        for k, cap in ((1, 10), (2, 3), (3, 1)):
            for vs in it.combinations(points(A), k):
                u = mask(vs)
                put(('exact-anchor', A, u), {i: 1 for i, s in enumerate(traces) if s & A == u},
                    cap - sum(B & A == u for B in g['star']))
        for u, v in it.combinations(points(A), 2):
            base = sum((B >> u & 1) + (B >> v & 1) for B in g['star'])
            put(('actual-anchor-pair19', A, u, v),
                {i: -((s >> u & 1) + (s >> v & 1)) for i, s in enumerate(traces)}, base - 19)
        if crowding_imports:
            for triple in it.combinations(points(A), 3):
                singles = tuple(1 << v for v in triple)
                put(('imported-crowding26', A, triple),
                    {i: 1 for i, s in enumerate(traces) if s & A in singles},
                    26 - sum(B & A in singles for B in g['star']))

    # These shared pool statements are invoked only for the P10 side.  An I8
    # may have a two-point transversal, so the same proof is not assumed on Z.
    ypool = [i for i, s in enumerate(traces) if (s & Y).bit_count() == 1]
    put(('Y-pool-H27',), dict.fromkeys(ypool, 1), 27)
    for u, v in it.combinations(range(6), 2):
        put(('Y-imported-cross15' if crowding_imports else 'Y-HP16-size68-cap18', u, v),
            {i: 1 for i, s in enumerate(traces) if s & Y in (1 << u, 1 << v)},
            15 if crowding_imports else 16)
    for v in range(6):
        h = [i for i, s in enumerate(traces) if s & Y == 1 << v]
        pair = [i for i, s in enumerate(traces) if (s & Y).bit_count() == 2 and s >> v & 1]
        put(('Y-singleton-cap10', v), dict.fromkeys(h, 1), 10)
        put(('Y-pair-pool6', v), dict.fromkeys(pair, 1), 6)
        cs = dict.fromkeys(pair, 9)
        cs.update(dict.fromkeys(h, 5))
        put(('Y-pair-singleton-affine', v), cs, 59)
        put(('Y-pool-affine', v), {i: 2 + 7 * (traces[i] & Y == 1 << v) for i in ypool}, 110)

    internal, removable, cover_internal = {}, {}, {}
    for v in range(core_size):
        component = Y if v < 6 else z
        internal[v] = [i for i, s in enumerate(traces)
                       if s.bit_count() == 4 and s >> v & 1 and s & component == s]
        removable[v] = []
        cover_internal[v] = []
        shape = g['shapes'][v]
        if shape == 'C5':
            cover_internal[v] = [i for i in internal[v]
                                 if all((traces[i] ^ (1 << v)) & e for e in g['edges'][v])]
            put(('literal-C5-degree-minus-covers15', v),
                {i: 1 for i in incidence[v] if i not in cover_internal[v]}, 15 - fixed_degree[v])
        elif shape == 'P5':
            cover = g['covers'][v]
            removable[v] = [i for i in internal[v] if traces[i] & cover != cover]
            put(('literal-P5-degree-minus-removable16', v),
                {i: 1 for i in incidence[v] if i not in removable[v]}, 16 - fixed_degree[v])

    # The complete triangle-plus-P3 five-star lemma: deleting its three
    # possible internal completions leaves degree at most15, on any support.
    hub_completions = {}
    if kind == 'Q8':
        for v in (6, 7):
            ids = [i for i in internal[v]
                   if all((traces[i] ^ (1 << v)) & edge for edge in g['edges'][v])]
            if len(ids) != 3:
                raise ValueError('Q8 hub has unexpected completion catalogue')
            hub_completions[v] = ids
            put(('triangle-path-hub-degree-minus-completions15', v),
                {i: 1 for i in incidence[v] if i not in ids}, 15 - fixed_degree[v])

    # Global trace incidence already shares actual degrees at the level of
    # their means.  Optional distribution ties strengthen that coherence but
    # can slow the LP substantially, so they are disabled by default.
    selectors, degree_choices = {}, {}
    for v in range(n):
        cap = 15 if v < 6 else 18
        if v in hub_completions:
            cap = min(cap, 15 + sum(int(hi[i]) for i in hub_completions[v]))
        minimum = max(7, fixed_degree[v] + sum(int(lo[i]) for i in incidence[v]))
        ds = tuple(range(minimum, cap + 1))
        degree_choices[v] = ds
        if not degree_distributions:
            continue
        cols = tuple(range(len(bounds), len(bounds) + len(ds)))
        selectors[v] = dict(zip(ds, cols))
        bounds.extend([(0, 1)] * len(cols))
        eq(dict.fromkeys(cols, 1), 1)
        cs = dict.fromkeys(incidence[v], 1)
        cs.update({j: -d for d, j in selectors[v].items()})
        eq(cs, -fixed_degree[v])

    sizes = []
    for T in g['link']:
        data = local_catalog(kind, T, crowding_imports)
        cat = data['rows']
        pts = points(T)
        features = [mask(vs) for vs in it.combinations(pts, 2)] + [T] + [1 << v for v in pts]
        buckets = [[i for i, s in enumerate(traces) if s & T == u] for u in features]
        alive = np.ones(len(cat), dtype=bool)
        for f, ids in enumerate(buckets):
            alive &= (cat[:, f] >= sum(lo[ids])) & (cat[:, f] <= sum(hi[ids]))
        for f, v in enumerate(pts):
            for key, ids in (('internal', internal[v]), ('removable', removable[v]),
                             ('covers', cover_internal[v])):
                alive &= data[key][:, f] <= sum(hi[ids])
            alive &= np.isin(data['degrees'][:, f], degree_choices[v])
            if v in hub_completions:
                cap_near = 5 + sum(int(hi[i]) for i in hub_completions[v])
                alive &= (cat[:, 4 + f] < 8) | (data['near'][:, f] <= cap_near)
        live = {key: values[alive] for key, values in data.items()}
        cols = tuple(range(len(bounds), len(bounds) + len(live['rows'])))
        sizes.append(len(cols))
        bounds.extend([(0, 1)] * len(cols))
        eq(dict.fromkeys(cols, 1), 1)
        for f, ids in enumerate(buckets):
            cs = dict.fromkeys(ids, 1)
            cs.update({j: -int(w) for j, w in zip(cols, live['rows'][:, f]) if w})
            eq(cs, 0)
        for f, v in enumerate(pts):
            for d, j in selectors.get(v, {}).items():
                cs = {j: -1}
                cs.update({a: 1 for a, value in zip(cols, live['degrees'][:, f]) if value == d})
                eq(cs, 0)
            for key, ids in (('internal', internal[v]), ('removable', removable[v]),
                             ('covers', cover_internal[v])):
                if g['shapes'][v] is None or not np.any(live[key][:, f]):
                    continue
                cs = dict.fromkeys(ids, -1)
                cs.update({j: int(w) for j, w in zip(cols, live[key][:, f]) if w})
                put(('literal-star-cost', key, T, v), cs, 0)
            if g['shapes'][v] in ('C5', 'P5'):
                component = Y if v < 6 else z
                cs = {i: -1 for i, s in enumerate(traces) if s & component == 1 << v}
                cs.update({j: int(w) for j, w in zip(cols, live['pool_lower'][:, f]) if w})
                put(('whole-component-singleton-lower', T, v), cs, 0)
            if v < 6:
                cs = dict.fromkeys(ypool, 1)
                cs.update({j: {9: 5, 10: 7}[int(row[4 + f])]
                           for j, row in zip(cols, live['rows']) if row[4 + f] >= 9})
                put(('Y-pool-conditional', T, v), cs, 27)

    def matrix(rows):
        rr, cc, vv = [], [], []
        for i, (terms, _) in enumerate(rows):
            for j, w in terms.items():
                rr.append(i)
                cc.append(j)
                vv.append(w)
        mat = coo_matrix((np.asarray(vv, dtype=float), (rr, cc)),
                         shape=(len(rows), len(bounds))).tocsr()
        return mat, np.asarray([rhs for _, rhs in rows], dtype=float)
    A, b = matrix(upper)
    E, f = matrix(equal)
    return traces, bounds, A, b, E, f, labels, sizes


def premises(kind, case, empty_z, assigned_z, forbidden, forbid_four_core,
             degree_distributions=False, crowding_imports=True):
    return [
        'F is a finite simple SF4 family; empty sunflower cores are forbidden.',
        'v4 additionally uses the complete triangle-plus-path star lemma: hub degree minus its three I00 completions is at most15; at singleton>=8 the intersecting near size is at most5 plus those completions.',
        'v3: minimum used degree7, small-complete-core trace H27, guarded Z cross15 and clique-H27 rows are justified in D18-additional-core-rows.md.',
        '|F| >= 68, d(x)=18, and the global maximum point degree is at most 18.',
        f'The complete root link is the recorded disjoint P10 + {kind}.',
        'H27, exact-anchor caps 10/3/1, global incidence caps 18/6/2, and the universal local43 structural lemmas are imported.',
        'Every actual anchor has closed neighbourhood at least 41 and each pair in it has degree sum at least 19.',
        'All four-point members wholly inside Y are absent. This imports the new mu41 P10-internal exclusions; this script does not replay them.',
        'All Z internals remain free except the explicit branch restrictions below.',
        'C5/P5 costs and whole-component singleton lower bounds use the ordinary lemmas in D18-structural-tools.md and literal six-point-support checks.',
        'When s>=8 or d>=17 and k is 8,9,10, the complete rooted point-link graph must occur in the classified intersecting I_k templates; no I7 graph classification is used.',
        'Y singleton-pool H27, 5h+9b<=59, b<=6, 2P+7h<=110 and conditional pool penalties use the ordinary P10 proofs in that note.',
        'The fifteen Y pair-pool HP16 rows additionally use the ordinary near-doubled-P10 argument in D18-pool-research.md under |F|>=68 and global degree cap18.',
        ('Prior-art cross15 and crowding26 are enabled: Y pair-pool sums are at most15, and the three largest exact singleton counts at each actual anchor sum to at most26. The written arbitrary-support bridge and Oct20 normal/optimized replays are imported, hash-bound dependencies, not rerun here.'
         if crowding_imports else 'Prior-art cross15 and crowding26 imports are disabled; the ordinary HP16 pool bound remains.'),
        'The local43 call uses emin=17 and bootstrap parameters r10=r9=0; the prior μ41/cap18 minimum used degree7 is imported; no finite exterior support is assumed.',
        dict(case=case, actual_marker=marker_catalogue(kind)[case]['marker'],
             empty_z=bool(empty_z), assigned_z=None if assigned_z is None else list(assigned_z),
             forbidden=list(forbidden), forbid_four_core=bool(forbid_four_core),
             degree_distributions=bool(degree_distributions), crowding_imports=bool(crowding_imports)),
    ]


def run(kind, case='none', seconds=30, empty_z=False, assigned_z=None,
        forbidden=(), forbid_four_core=False, label=None, degree_distributions=False,
        crowding_imports=True):
    """One explicitly requested numerical case; integer-box diagnostic only."""
    if not 0 < seconds <= 30:
        raise ValueError('Per-solver limit must be in (0,30] seconds')
    from scipy.optimize import linprog
    start = time.monotonic()
    tr, bounds, A, b, E, f, labels, sizes = build(
        kind, case, empty_z, assigned_z, forbidden, forbid_four_core,
        degree_distributions, crowding_imports)
    N = len(tr)
    built_seconds = time.monotonic() - start
    print(json.dumps(dict(phase='built', kind=kind, case=case, columns=len(bounds),
                          rows=len(b), catalogue_sizes=sizes, seconds=built_seconds)), flush=True)
    c = np.zeros(len(bounds))
    c[:N] = -1
    result = linprog(c, A_ub=A, b_ub=b, A_eq=E, b_eq=f, bounds=bounds,
                     method='highs', options={'time_limit': seconds})
    record = dict(kind=kind, case=case, empty_z=empty_z, assigned_z=assigned_z,
                  forbidden=list(forbidden), forbid_four_core=forbid_four_core,
                  degree_distributions=degree_distributions,
                  crowding_imports=crowding_imports,
                  status=int(result.status), message=result.message,
                  target_residuals=50, point_cap=18, mu=41, columns=len(bounds),
                  trace_columns=N, upper_rows=len(b), equal_rows=len(f),
                  catalogue_sizes=sizes, build_seconds=built_seconds,
                  solver_time_limit_seconds=seconds, seconds=time.monotonic() - start,
                  source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  imported_local43_sha256=hashlib.sha256(LOCAL43.read_bytes()).hexdigest(),
                  structural_note_sha256=hashlib.sha256((HERE / 'D18-structural-tools.md').read_bytes()).hexdigest(),
                  pool_note_sha256=hashlib.sha256((HERE / 'D18-pool-research.md').read_bytes()).hexdigest(),
                  literal_premises=premises(kind, case, empty_z, assigned_z, forbidden,
                                            forbid_four_core, degree_distributions, crowding_imports),
                  geometry=catalogue_metadata(kind),
                  assurance='Numerical discovery with an exact integer-box diagnostic of this conditional relaxation; not independent reconstruction, Lean, or a complete branch proof.')
    if crowding_imports:
        record['imported_crowding_sources'] = {
            name: dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            for name, path in CROWDING_SOURCES.items()}
    if result.status == 0:
        scale = 10**10
        ys = [max(0, round(-float(v) * scale)) for v in result.ineqlin.marginals]
        es = [round(-float(v) * scale) for v in result.eqlin.marginals]
        q = [0] * len(bounds)
        for mat, weights in ((A, ys), (E, es)):
            for i, w in enumerate(weights):
                if not w:
                    continue
                for entry in range(mat.indptr[i], mat.indptr[i + 1]):
                    value = float(mat.data[entry])
                    if not value.is_integer():
                        raise ValueError('Noninteger matrix coefficient in exact-box diagnostic')
                    q[int(mat.indices[entry])] += w * int(value)
        for values in (b, f):
            if any(not float(value).is_integer() for value in values):
                raise ValueError('Noninteger RHS in exact-box diagnostic')
        H = sum(w * int(v) for w, v in zip(ys, b)) + sum(w * int(v) for w, v in zip(es, f))
        correction = sum(max(l * ((scale if j < N else 0) - q[j]),
                             u * ((scale if j < N else 0) - q[j]))
                         for j, (l, u) in enumerate(bounds))
        record['solver_upper'] = -float(result.fun)
        record['dual'] = dict(scale=scale, H=H, correction=correction,
                              upper_numerator=H + correction,
                              below50=H + correction < 50 * scale,
                              display=(H + correction) / scale,
                              inequality_sign='nonnegative weights on A*x<=b',
                              equality_sign='signed weights on E*x=f',
                              ineq=[[i, w, labels[i]] for i, w in enumerate(ys) if w],
                              eq=[[i, w] for i, w in enumerate(es) if w])
        record['primal_trace'] = [[s, float(value)] for s, value in zip(tr, result.x[:N]) if value > 1e-7]
    output = HERE / 'degree18_p10'
    output.mkdir(exist_ok=True)
    if label is not None and (not label or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-' for c in label)):
        raise ValueError('Receipt label must be a simple filename stem')
    identity = dict(source_sha256=record['source_sha256'],
                    imported_local43_sha256=record['imported_local43_sha256'],
                    structural_note_sha256=record['structural_note_sha256'],
                    pool_note_sha256=record['pool_note_sha256'],
                    imported_crowding_sources=record.get('imported_crowding_sources', {}),
                    kind=kind, literal_premises=record['literal_premises'])
    fingerprint = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    record['premise_sha256'] = fingerprint
    stem = f'{kind}-{case}' + (f'-{label}' if label else '') + f'-{fingerprint[:12]}'
    destination = output / (stem + '.json')
    if destination.exists():
        raise FileExistsError(f'Refusing to overwrite an existing receipt: {destination}')
    destination.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(dict(receipt=str(destination), status=record['status'],
                          upper=record.get('dual', {}).get('display'),
                          below50=record.get('dual', {}).get('below50'),
                          seconds=record['seconds'])), flush=True)
    return record


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kind', choices=KINDS, required=True)
    ap.add_argument('--case', default='none')
    action = ap.add_mutually_exclusive_group()
    action.add_argument('--catalogue', action='store_true', help='Print the full marker catalogue; default action')
    action.add_argument('--build-only', action='store_true', help='Build one relaxation without solving it')
    action.add_argument('--solve', action='store_true', help='Explicitly run one numerical discovery case')
    ap.add_argument('--seconds', type=float, default=30)
    ap.add_argument('--empty-z', action='store_true')
    ap.add_argument('--assigned-z', help='JSON list of masks for a complete assigned Z-internal pattern')
    ap.add_argument('--forbidden', default='[]', help='JSON list of individual forbidden trace masks')
    ap.add_argument('--forbid-four-core', action='store_true', help='Additional premise: every four-core residual is absent')
    ap.add_argument('--degree-distributions', action='store_true',
                    help='Optional stronger shared degree distributions; disabled by default')
    crowding = ap.add_mutually_exclusive_group()
    crowding.add_argument('--crowding-imports', dest='crowding_imports', action='store_true',
                          default=True, help='Use replayed prior-art cross15/crowding26 imports (default)')
    crowding.add_argument('--no-crowding-imports', dest='crowding_imports', action='store_false',
                          help='Disable prior-art cross15/crowding26 imports')
    ap.add_argument('--label')
    args = ap.parse_args()
    if args.case not in marker_catalogue(args.kind):
        ap.error('Unknown marker case; request --catalogue first')
    assigned = None if args.assigned_z is None else json.loads(args.assigned_z)
    forbidden = json.loads(args.forbidden)
    if not isinstance(forbidden, list) or any(type(v) is not int or v < 0 for v in forbidden):
        ap.error('--forbidden must be a JSON list of nonnegative integer masks')
    if assigned is not None and (not isinstance(assigned, list) or any(type(v) is not int or v < 0 for v in assigned)):
        ap.error('--assigned-z must be a JSON list of nonnegative integer masks')
    if args.solve:
        run(args.kind, args.case, args.seconds, args.empty_z, assigned,
            forbidden, args.forbid_four_core, args.label,
            args.degree_distributions, args.crowding_imports)
    elif args.build_only:
        start = time.monotonic()
        tr, bounds, A, b, E, f, labels, sizes = build(
            args.kind, args.case, args.empty_z, assigned, forbidden,
            args.forbid_four_core, args.degree_distributions, args.crowding_imports)
        print(json.dumps(dict(kind=args.kind, case=args.case, traces=len(tr), columns=len(bounds),
                              upper_rows=len(b), equal_rows=len(f), catalogue_sizes=sizes,
                              seconds=time.monotonic() - start,
                              literal_premises=premises(args.kind, args.case, args.empty_z, assigned,
                                                       forbidden, args.forbid_four_core,
                                                       args.degree_distributions,
                                                       args.crowding_imports)), indent=2))
    else:
        print(json.dumps(catalogue_metadata(args.kind), indent=2))


if __name__ == '__main__':
    main()
