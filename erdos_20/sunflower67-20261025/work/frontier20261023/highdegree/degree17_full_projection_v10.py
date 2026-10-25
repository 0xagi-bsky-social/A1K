#!/usr/bin/env python3
"""Degree17 projection v9: actual P9 copied-block cross-star rows.

No solver runs on import or without the explicit --solve flag.  The default
action prints a finite marker catalogue. P10-side internals are absent under
the separate D17 component exclusion; P9-side and opposite internals are free.
The opposite I7 catalogue is bound to an independent finite census and its
ordinary arbitrary-support reduction. This version retains v2's universal
two-anchor triangle inequalities and adds optional literal H27 cliques from
a hash-bound discovery JSON. Every pair, including self-pairs, is rechecked
against receiving-branch actual members. Discovery weights are ignored.
A literal disjoint pair of fixed near triples forces exact singleton cap7;
the same witnesses prune the receiving local selector catalogue.
Additional actual residual members may be selected without assigning the
complete Z-internal pattern. Their union determines the represented universe,
with at most the one canonical extra point. All fixed-member rows see them.
The entire root-avoiding residual family with at most one Y point is
intersecting, by a prescribed P9/P10 cone avoiding two Y points, and has
size at most27. This unconditional row is added separately from Y-pool-H27.
For a literal P9 component, each fixed actual member outside x+Y has
disjoint complement at most22, by the complete P9+K ordinary lemma.
Literal surviving outside-link cones sharpen this cap by the ordinary
20+k, empty-intersection and singleton-intersection bounds. Both its
disjoint-cap and corresponding neighbourhood rows retain root offsets.
At every represented exterior centre z, the actual H+B copies and the
actual H+C copies are separately bounded by6 using cross-star HP15.

Version10 adds only the three conditional Q8 empty-Z triad degree16 rows.
Universal structural statements and the ordinary C5/P5/pool lemmas are imported
premises.  A rounded integer dual only certifies its stated finite relaxation.
The target is residual51 with root/global cap17 and mu41. Prior crowding26,
cross15 and minimum used degree7 are explicit imports. No exterior support
bound is imposed. Adapted from the frozen D18 v4 source, not imported from it.
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
    'D17_route': HERE / 'D17-I7-classification-route.md',
    'I7_certificate': REPOSITORY / 'companion/terminal/r16/results/seven_certificate.json',
    'I7_upstream_checker': REPOSITORY / 'companion/terminal/r16/src/check_seven.py',
    'I7_independent_checker': HERE / 'D17_i7_coverage.py',
    'I7_independent_receipt': HERE / 'D17-i7-coverage.json',
    'R16_prior_normal_output': REPOSITORY.parent / 'replay-selected-20261020/terminal_r16_normal/stdout.json',
    'R16_prior_optimized_output': REPOSITORY.parent / 'replay-selected-20261020/terminal_r16_optimized/stdout.json',
    'adaptation_source_D18_v4': HERE / 'degree18_p10_projection_v4.py',
    'adaptation_source_D17_v1': HERE / 'degree17_full_projection.py',
    'two_actual_anchor_triangle_bridge': HERE / 'D18-I06-triangle-closure.md',
    'D17_full_family_bridge': HERE / 'D17-full-model-bridge.md',
    'adaptation_source_D17_v2': HERE / 'degree17_full_projection_v2.py',
    'D17_H27_clique_bridge': HERE / 'D17-H27-clique-addon.md',
    'trace_H27_general_bridge': HERE / 'TRACE-H27-CLIQUE-SEPARATION.md',
    'trace_H27_separator': HERE / 'trace_h27_cliques.py',
    'adaptation_source_D17_v3': HERE / 'degree17_full_projection_v3.py',
    'marked_B4_general_bridge': HERE / 'D18-marked-B4-row.md',
    'D17_marked_B4_bridge': HERE / 'D17-marked-B4-addon.md',
    'adaptation_source_D17_v4': HERE / 'degree17_full_projection_v4.py',
    'D17_extra_actual_members_bridge': HERE / 'D17-H7-equality-extra-members.md',
    'adaptation_source_D17_v5': HERE / 'degree17_full_projection_v5.py',
    'D17_whole_zero_or_one_Y_H27_bridge': HERE / 'D17-Y-at-most-one-H27.md',
    'adaptation_source_D17_v6': HERE / 'degree17_full_projection_v6.py',
    'P9_disjoint_complement22_bridge': HERE / 'P9-disjoint-complement22.md',
    'D17_P9_complement22_projection_bridge': HERE / 'D17-P9-complement22-addon.md',
    'adaptation_source_D17_v7': HERE / 'degree17_full_projection_v7.py',
    'P9_literal_complement_profile_bridge': HERE / 'P9-literal-complement-profile.md',
    'adaptation_source_D17_v8': HERE / 'degree17_full_projection_v8.py',
    'D17_P9_actual_copy_cross15_bridge': HERE / 'D17-P9-copy-cross15.md',
    'adaptation_source_D17_v9': HERE / 'degree17_full_projection_v9.py',
    'D17_C4_internal_completion_bridge': HERE / 'D17-C4-internal-completion.md',
    'D17_C4_literal_checker': HERE / 'check_D17_C4_completion.py',
    'D17_C4_literal_receipt': HERE / 'D17-C4-completion-literal.json',
}
sys.path.insert(0, str(LOCAL43.parent))
import local43 as L

ROOT = 15
X = 1 << ROOT
Y = (1 << 6) - 1
KINDS = tuple(f'P10-H{i}' for i in range(8)) + ('P9-P8-i1', 'P9-P8-i2', 'P9-Q8')
ROOT_DEGREE = 17
POINT_CAP = 17
TARGET = 51


def mask(vs):
    return sum(1 << v for v in vs)


def points(s):
    return tuple(v for v in range(s.bit_length()) if s >> v & 1)


def move(s, permutation):
    return mask(permutation[v] for v in points(s))


def h27_clique_input(path, expected_sha256=None):
    """Read once and bind row bytes; no discovery weight is a mathematical input.

    Return (payload, dependency). Replayers should supply the recorded hash to
    build's h27_cliques_sha256 argument before reconstructing any matrix.
    """
    if path is None:
        if expected_sha256 is not None:
            raise ValueError('A clique hash requires a clique file')
        return None, None
    path = pathlib.Path(path).resolve()
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if expected_sha256 is not None and digest != expected_sha256:
        raise ValueError('H27 clique input hash changed')
    data = json.loads(raw)
    if not isinstance(data, dict) or data.get('schema') != 'trace-h27-clique-discovery-v1':
        raise ValueError('Unsupported H27 clique input schema')
    if type(data.get('threshold')) is not int or data['threshold'] != 27:
        raise ValueError('H27 input must use the literal threshold27')
    if not isinstance(data.get('clique_rows'), list) or not data['clique_rows']:
        raise ValueError('H27 input must contain an explicit nonempty row list')
    sources = {}
    for key, source in (
            ('separator_source_sha256', HERE / 'trace_h27_cliques.py'),
            ('ordinary_note_sha256', HERE / 'TRACE-H27-CLIQUE-SEPARATION.md')):
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if data.get(key) != actual:
            raise ValueError(f'H27 discovery source mismatch: {key}')
        sources[key] = dict(path=str(source), sha256=actual)
    dependency = dict(path=str(path), sha256=digest, schema=data['schema'],
                      source_kind=data.get('kind'), source_case=data.get('case'),
                      represented_points=data.get('represented_points'),
                      excluded_points=data.get('excluded_points'),
                      fixed_members=data.get('fixed_members'),
                      clique_row_count=len(data['clique_rows']), sources=sources,
                      transfer_policy='same universe, or root-only core-to-one-marker restriction lift; literal pair validation required')
    return data, dependency


def validated_h27_rows(data, g, n, fixed, traces):
    """Validate actual witnesses and return fine-trace coefficient-one rows.

    The only permitted refinement adds the receiving branch's one actual
    exterior marker to the complete root core; source witnesses must then be
    root cones. The row aggregates every fine trace restricting to a source
    clique trace. Arbitrary relabeling, coarsening and other lifts fail closed.
    """
    if data is None:
        return []
    if data.get('kind') != g['kind']:
        raise ValueError('H27 clique geometry kind does not match the receiving branch')
    represented = data.get('represented_points')
    if (not isinstance(represented, list)
            or any(type(v) is not int or not 0 <= v < ROOT for v in represented)
            or represented != sorted(set(represented))):
        raise ValueError('H27 represented points must be distinct sorted receiving-universe labels')
    excluded = data.get('excluded_points')
    if excluded != [ROOT] or any(type(v) is not int for v in excluded):
        raise ValueError('H27 excluded points must be exactly the receiving residual root')
    if ROOT in represented:
        raise ValueError('The excluded root cannot be a represented residual point')
    source_universe = mask(represented)
    same_universe = represented == list(range(n))
    root_marker_lift = (represented == list(range(g['core_size']))
                        and n == g['core_size'] + 1)
    if not (same_universe or root_marker_lift):
        raise ValueError('Unsupported H27 represented-universe transfer')
    witnesses = data.get('fixed_members')
    if (not isinstance(witnesses, list)
            or any(type(B) is not int or B < 0 or B.bit_count() != 4 for B in witnesses)
            or len(set(witnesses)) != len(witnesses)):
        raise ValueError('H27 fixed members must be distinct literal four-sets')
    if not set(witnesses) <= set(fixed):
        raise ValueError('An H27 witness is not actual in the receiving branch')
    if any(B & ~(source_universe | X) for B in witnesses):
        raise ValueError('An H27 witness contains an unrepresented, nonexcluded point')
    if root_marker_lift and not set(witnesses) <= set(g['star']):
        raise ValueError('Only root-cone witnesses may transfer to a larger marker universe')

    @lru_cache(None)
    def forced_meeting(a, b):
        return bool(a & b) or any(not (B & (a | b)) for B in witnesses)

    rows = []
    seen = set()
    for number, row in enumerate(data['clique_rows']):
        if not isinstance(row, dict) or type(row.get('upper')) is not int or row['upper'] != 27:
            raise ValueError('Each H27 row must have literal upper27')
        clique = row.get('trace_masks')
        if (not isinstance(clique, list) or not clique
                or any(type(s) is not int or s < 0 or s.bit_count() > 4
                       or s & ~source_universe for s in clique)
                or len(set(clique)) != len(clique)):
            raise ValueError('H27 row has invalid, duplicate or out-of-universe traces')
        clique = tuple(sorted(clique))
        if clique in seen:
            raise ValueError('Duplicate H27 clique rows are not accepted')
        seen.add(clique)
        if not all(forced_meeting(a, b) for a, b in it.combinations_with_replacement(clique, 2)):
            raise ValueError(f'H27 clique row{number} fails an actual pair/diagonal witness')
        member = set(clique)
        coefficients = {i: 1 for i, t in enumerate(traces) if t & source_universe in member}
        if not coefficients:
            raise ValueError('H27 row maps to no receiving trace')
        row_hash = hashlib.sha256(json.dumps(clique, separators=(',', ':')).encode()).hexdigest()
        rows.append((('external-literal-H27-trace-clique', number, row_hash), coefficients, 27))
    return rows


P10 = tuple(mask(map(int, t)) for t in
            '012 015 023 034 045 124 134 135 235 245'.split())
Q8 = tuple(mask((h, *ab)) for h in (0, 1)
           for ab in it.combinations((2, 3, 4), 2)) + (mask((0, 1, 5)), mask((0, 1, 6)))


@lru_cache(None)
def i7_templates():
    path = CROWDING_SOURCES['I7_certificate']
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != 'fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164':
        raise ValueError('Frozen I7 certificate changed')
    receipt = json.loads(CROWDING_SOURCES['I7_independent_receipt'].read_text())
    if (receipt['status'] != 'PASS_INDEPENDENT_FINITE_I7_COVERAGE'
            or receipt['imported_certificate_sha256'] != digest
            or receipt['source_sha256'] != hashlib.sha256(CROWDING_SOURCES['I7_independent_checker'].read_bytes()).hexdigest()
            or receipt['six_point_candidates'] != 77520
            or receipt['labelled_six_point_families'] != 1860
            or receipt['orbit_sizes'] != [120, 360, 60, 240, 360, 360, 360]
            or receipt['mixed_traces'] != 175):
        raise ValueError('Independent I7 coverage receipt does not match its sources')
    data = json.loads(path.read_text())
    if [r['id'] for r in data['rows']] != list(range(8)):
        raise ValueError('Missing I7 template')
    return tuple(tuple(mask(t) for t in row['blocks']) for row in data['rows'])


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
    """Rooted graphs in classified I7/I8/I9/I10, with complete I7 coverage."""
    if k not in (7, 8, 9, 10):
        raise ValueError('No rooted template classification below seven')
    families = list(i7_templates()) if k == 7 else list(it.combinations(P10, k))
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
        raise ValueError('Unknown degree17 complete-link kind')
    p8 = p8_deletion_types()
    empty_y = kind.startswith('P10-')
    ylink = P10 if empty_y else P10[1:]
    if empty_y:
        number = int(kind.split('-H')[1])
        local_z = i7_templates()[number]
        z_size = 7 if number == 7 else 6
        p8_key = None
    else:
        p8_key = kind[3:]
        local_z = Q8 if p8_key == 'Q8' else p8[p8_key]['link']
        z_size = 7 if p8_key == 'Q8' else 6
    core_size = 6 + z_size
    z = mask(range(6, core_size))
    zlink = tuple(t << 6 for t in local_z)
    link = ylink + zlink
    if len(link) != ROOT_DEGREE:
        raise ValueError('Incomplete root degree17 link')
    star = tuple(X | t for t in link)
    ya = automorphisms(ylink, 6)
    za = automorphisms(local_z, z_size)
    # The canonical exterior marker is fixed.  The root is outside this domain.
    group = tuple(p + tuple(v + 6 for v in q) + (core_size,)
                  for p, q in it.product(ya, za))
    shapes, covers, edges = {}, {}, {}
    for v in range(core_size):
        component, support = (ylink, Y) if v < 6 else (zlink, z)
        shapes[v], covers[v] = literal_star_kind(component, v, support)
        edges[v] = tuple(t ^ (1 << v) for t in component if t >> v & 1)
    if empty_y and any(shapes[v] != 'C5' for v in range(6)):
        raise ValueError('Canonical P10 has an unexpected point-link')
    if kind == 'P9-Q8' and any(shapes[v] is not None for v in range(6, core_size)):
        raise ValueError('Q8 has been incorrectly assigned a C5/P5 cut')
    signatures = {v: graph_signature(tuple(sorted(edges[v]))) for v in edges}
    hub_signature = graph_signature((mask((0, 1)), mask((0, 2)), mask((1, 2)),
                                     mask((3, 4)), mask((3, 5))))
    hubs = tuple(v for v in range(core_size)
                 if signatures[v] == hub_signature
                 and (6 if v < 6 else z_size) == 7)
    return dict(kind=kind, z=z, z_size=z_size, core_size=core_size,
                ylink=ylink, zlink=zlink, empty_y=empty_y, hub_vertices=hubs,
                exterior=core_size, link=link, star=star, group=group,
                y_aut_order=len(ya), z_aut_order=len(za), shapes=shapes,
                covers=covers, edges=edges,
                graph_signatures=signatures,
                omitted=p8[p8_key]['omitted'] if p8_key in p8 else (),
                deletion_orbit=p8[p8_key]['deletion_orbit'] if p8_key in p8 else ())


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
    domains = (('IY', 'internal-Y', set() if g['empty_y'] else yinternal),
               ('IZ', 'internal-Z', zinternal), ('E4_', 'mixed-four-core', mixed4),
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
    if total != (all4 - (yinternal if g['empty_y'] else set())) | mixed3:
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
                excluded_Y_internal_count=15 if g['empty_y'] else 0,
                triangle_path_hub_vertices=list(g['hub_vertices']),
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
            if sx + k[0] != ROOT_DEGREE:
                raise ValueError('Root link is not complete degree17')
            if sx not in L.local_s_candidates(0, p, t, 17, 0, 0):
                continue
            candidates = [tuple(s for s in L.local_s_candidates(i, p, t, 17, 0, 0)
                                if s + k[i] <= POINT_CAP) for i in (1, 2, 3)]
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
                    # whenever K is intersecting and k>=7. All eight I7
                    # templates are included, including its seven-point type.
                    if (k[j] in (7, 8, 9, 10) and (s[j] >= 8 or d[j] >= 17)
                            and g['graph_signatures'][v] not in intersecting_point_link_templates(k[j])):
                        good = False
                        break
                    # The empty P10 internal premise is applied only on Y.
                    if g['empty_y'] and v < 6 and (d[j] > 15 or (s[j] >= 8 and k[j] > 5)):
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


def fixed_near_disjoint_witness(fixed, anchor, vertex):
    """Return actual B,C with disjoint near triples in the complete v-link."""
    bit = 1 << vertex
    if not anchor & bit:
        raise ValueError('The singleton pivot must belong to its actual anchor')
    near = [B for B in fixed if B & bit and (B & anchor) != bit]
    return next(((B, C) for B, C in it.combinations(near, 2) if B & C == bit), None)


def normalize_extra_members(extra_members, g):
    """Canonical literal residual four-sets, not a complete internal assignment.

    Each entry is either an integer mask or an explicit four-label list/tuple.
    The sole permitted noncore label is g['exterior']; all other exterior
    points remain unrepresented and are counted with arbitrary multiplicity.
    """
    if not isinstance(extra_members, (list, tuple)):
        raise ValueError('Extra members must be an explicit list or tuple')
    result = []
    allowed = (1 << (g['core_size'] + 1)) - 1
    for member in extra_members:
        if type(member) is int:
            value = member
        elif isinstance(member, (list, tuple)):
            if (len(member) != 4 or any(type(v) is not int or not 0 <= v <= g['exterior']
                                       for v in member) or len(set(member)) != 4):
                raise ValueError('An extra member must have four distinct allowed point labels')
            value = mask(member)
        else:
            raise ValueError('An extra member must be a mask or a four-label list')
        if value < 0 or value.bit_count() != 4 or value & ~allowed or value & X:
            raise ValueError('An extra member must be a residual four-set on core plus its one canonical exterior point')
        result.append(value)
    if len(set(result)) != len(result):
        raise ValueError('Extra actual members must be distinct')
    return tuple(sorted(result))


def selected_members(kind, case, assigned_z, extra_members):
    """Return the selected actual residuals and their full represented support."""
    g = geometry(kind)
    marker = marker_catalogue(kind)[case]['marker']
    extras = normalize_extra_members(extra_members, g)
    selected = ([] if marker is None else [marker]) + list(extras)
    if assigned_z is not None:
        if (not isinstance(assigned_z, (list, tuple))
                or any(type(s) is not int or s < 0 or s.bit_count() != 4
                       or s & g['z'] != s for s in assigned_z)
                or len(set(assigned_z)) != len(assigned_z)):
            raise ValueError('Assigned Z pattern must be distinct internal four-sets')
        selected.extend(assigned_z)
    selected = tuple(dict.fromkeys(selected))
    n = max((g['core_size'], *(s.bit_length() for s in selected)))
    if not g['core_size'] <= n <= g['core_size'] + 1 or n > ROOT:
        raise ValueError('Selected members exceed the supported actual-point universe')
    return extras, selected, n


def build(kind, case='none', empty_z=False, assigned_z=None, forbidden=(),
          forbid_four_core=False, degree_distributions=False, crowding_imports=True,
          h27_cliques=None, h27_cliques_sha256=None, extra_members=()):
    """Return traces,bounds,A,b,E,f,upper_labels,local_catalogue_sizes.

    Optional exclusions and a complete assigned-Z pattern are additional branch
    premises. With assigned_z=None all unselected Z internals remain free.
    Extra members are actual residual four-sets and impose only their presence.
    """
    if not crowding_imports:
        raise ValueError('D17 requires the explicitly imported prior crowding/minimum7/cross15 package')
    clique_data, _ = h27_clique_input(h27_cliques, h27_cliques_sha256)
    g = geometry(kind)
    core_size, z = g['core_size'], g['z']
    _, selected, n = selected_members(kind, case, assigned_z, extra_members)
    traces = tuple(mask(vs) for k in range(5) for vs in it.combinations(range(n), k))
    index = {s: i for i, s in enumerate(traces)}
    N = len(traces)
    lo = np.zeros(N, dtype=np.int64)
    hi = np.asarray([{0: 27, 1: POINT_CAP, 2: 6, 3: 2, 4: 1}[s.bit_count()]
                     for s in traces], dtype=np.int64)
    if assigned_z is not None:
        assigned_z = tuple(assigned_z)
        if empty_z and assigned_z:
            raise ValueError('Nonempty assigned Z pattern conflicts with empty_z')
    forbidden = tuple(forbidden)
    if any(s not in index for s in forbidden):
        raise ValueError('A forbidden trace lies outside this actual-point universe')
    for i, s in enumerate(traces):
        if s.bit_count() == 4:
            if (g['empty_y'] and s & Y == s) or (empty_z and s & z == s):
                hi[i] = 0
            if assigned_z is not None and s & z == s:
                lo[i] = hi[i] = int(s in assigned_z)
            if forbid_four_core and s < (1 << core_size):
                hi[i] = 0
        if s in forbidden:
            hi[i] = 0
    fixed = g['star'] + selected
    if any(A & B == A & C == B & C for A, B, C in it.combinations(fixed, 3)):
        raise ValueError('Selected actual members already form a sunflower')
    b4_singleton_guards = {}
    for anchor in fixed:
        for vertex in points(anchor):
            witness = fixed_near_disjoint_witness(fixed, anchor, vertex)
            if witness is not None:
                b4_singleton_guards[anchor, vertex] = witness
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
    for k, cap in ((1, POINT_CAP), (2, 6), (3, 2)):
        for vs in it.combinations(range(n), k):
            u = mask(vs)
            put(('incidence', u), {i: 1 for i, s in enumerate(traces) if s & u == u},
                cap - sum(T & u == u for T in g['link']))
    # Complete C4 at the root pair forces a Z-internal completion if
    # a Q8 triad point has degree17. Empty Z excludes that completion.
    if kind == 'P9-Q8' and empty_z:
        for v in (8, 9, 10):
            put(('Q8-empty-Z-C4-point-cap16', v), dict.fromkeys(incidence[v], 1),
                16 - fixed_degree[v])
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
    for label, terms, rhs in validated_h27_rows(clique_data, g, n, fixed, traces):
        put(label, terms, rhs)
    # A literally witnessed disjoint pair in the near triple link makes
    # exact singleton >=8 impossible by B4. Only root cones are offsets.
    for (anchor, vertex), (B, C) in b4_singleton_guards.items():
        bit = 1 << vertex
        put(('fixed-near-disjoint-B4-singleton7', anchor, vertex, B, C),
            {i: 1 for i, s in enumerate(traces) if s & anchor == bit},
            7 - sum(D & anchor == bit for D in g['star']))
    # The full root link, including K, is retained in this guard and offset.
    # The ordinary complement lemma does not require K to be an I8 template.
    p9_complement_guard = (g['ylink'] == P10[1:]
                           and g['link'] == g['ylink'] + g['zlink']
                           and all(not (T & Y) for T in g['zlink']))
    for A in fixed:
        if p9_complement_guard and not (A & (X | Y)):
            surviving = tuple(T for T in g['zlink'] if not (T & A))
            k = len(surviving)
            common = 0
            cap = 20 if k == 0 else min(22, 20 + k)
            if k:
                common = surviving[0]
                for T in surviving[1:]:
                    common &= T
                if not common:
                    cap = min(cap, 9 + k)
                elif common.bit_count() == 1:
                    cap = min(cap, 15 + k)
                elif k >= 3:
                    raise ValueError('Three actual K cones violate triple codegree2')
            root_disjoint = sum(not (B & A) for B in g['star'])
            root_meeting = len(g['star']) - root_disjoint
            if root_disjoint != 9 + k:
                raise ValueError('P9 complement profile lost a prescribed root cone')
            put(('actual-P9-outside-disjoint-profile', A, cap, k, common),
                {i: 1 for i, s in enumerate(traces) if not (s & A)},
                cap - root_disjoint)
            put(('actual-P9-outside-mu-profile', A, cap, k, common),
                {i: -1 for i, s in enumerate(traces) if s & A},
                root_meeting - (68 - cap))
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

    # Universal two-actual-anchor B4 triangle inequality. For R intersect M
    # equal to {h,m}, and k in R minus M, the exact m-singleton and km-pair
    # counts on R satisfy s+p-1[(M minus h) union k is actual] <= 12.
    # Only the complete fixed root star contributes a constant offset.
    for R, M in it.permutations(fixed, 2):
        overlap = R & M
        if overlap.bit_count() != 2:
            continue
        for m in points(overlap):
            mbit = 1 << m
            hbit = overlap ^ mbit
            h = points(hbit)[0]
            for k in points(R & ~M):
                pair = mbit | (1 << k)
                categories = (mbit, pair)
                companion = (M ^ hbit) | (1 << k)
                cs = {i: 1 for i, s in enumerate(traces) if s & R in categories}
                offset = sum(B & R in categories for B in g['star'])
                rhs = 12 - offset
                if companion & X:
                    # Completeness of the root link decides this membership.
                    rhs += int(companion in g['star'])
                else:
                    # A four-point trace is literal actual membership. The
                    # companion already occurs in the pair category, so this
                    # subtraction cancels its +1 rather than replacing it.
                    j = index[companion]
                    cs[j] = cs.get(j, 0) - 1
                put(('two-actual-anchor-triangle', R, M, h, m, k, companion), cs, rhs)

    # Two separate actual tail subfamilies; never combine complementary B,C.
    if p9_complement_guard:
        missing = P10[0]
        complementary = Y ^ missing
        for centre in range(n):
            if (1 << centre) & (X | Y):
                continue
            for exceptional in (missing, complementary):
                copies = tuple(index[T | (1 << centre)]
                               for T in g['ylink'] + (exceptional,))
                put(('P9-actual-copy-cross15', centre, exceptional),
                    dict.fromkeys(copies, 1), 6)

    # P10/P9 both have a block avoiding each point pair, so their whole-Y
    # singleton pool is intersecting. Z instead uses explicit guarded cliques.
    ypool = [i for i, s in enumerate(traces) if (s & Y).bit_count() == 1]
    put(('Y-pool-H27',), dict.fromkeys(ypool, 1), 27)
    # Two disjoint residuals each using at most one Y point admit a
    # prescribed P9/P10 root cone disjoint from both. The entire actual
    # residual family in these trace classes is therefore intersecting.
    # Root cones are excluded from the family, so there is no offset.
    put(('Y-at-most-one-H27',),
        {i: 1 for i, s in enumerate(traces) if (s & Y).bit_count() <= 1}, 27)
    for u, v in it.combinations(range(6), 2):
        put(('Y-imported-cross15' if crowding_imports else 'Y-HP16-size68-cap18', u, v),
            {i: 1 for i, s in enumerate(traces) if s & Y in (1 << u, 1 << v)},
            15 if crowding_imports else 16)
    for v in range(6):
        h = [i for i, s in enumerate(traces) if s & Y == 1 << v]
        put(('Y-singleton-cap10', v), dict.fromkeys(h, 1), 10)
        if g['shapes'][v] == 'C5':
            exclusions = (None,)
        elif g['shapes'][v] == 'P5':
            exclusions = points(g['covers'][v])
        else:
            raise ValueError('P10/P9 Y point-link is not a literal C5/P5')
        for ex in exclusions:
            pair = [i for i, s in enumerate(traces)
                    if (s & Y).bit_count() == 2 and s >> v & 1
                    and (ex is None or not s >> ex & 1)]
            put(('Y-pair-pool6', v, ex), dict.fromkeys(pair, 1), 6)
            cs = dict.fromkeys(pair, 9)
            cs.update(dict.fromkeys(h, 5))
            put(('Y-pair-singleton-affine', v, ex), cs, 59)
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
    for v in g['hub_vertices']:
        ids = [i for i in internal[v]
               if all((traces[i] ^ (1 << v)) & edge for edge in g['edges'][v])]
        if len(ids) != 3:
            raise ValueError('Literal triangle-path hub has unexpected cover completions')
        hub_completions[v] = ids
        put(('triangle-path-hub-degree-minus-completions15', v),
            {i: 1 for i in incidence[v] if i not in ids}, 15 - fixed_degree[v])

    # Global trace incidence already shares actual degrees at the level of
    # their means.  Optional distribution ties strengthen that coherence but
    # can slow the LP substantially, so they are disabled by default.
    selectors, degree_choices = {}, {}
    for v in range(n):
        cap = 15 if g['empty_y'] and v < 6 else POINT_CAP
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
        anchor = T | X
        if ((anchor, ROOT) in b4_singleton_guards
                and sum(B & anchor == X for B in g['star']) > 7):
            alive[:] = False
        for f, v in enumerate(pts):
            if (anchor, v) in b4_singleton_guards:
                alive &= cat[:, 4 + f] <= 7
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
             degree_distributions=False, crowding_imports=True, h27_cliques=None,
             extra_members=()):
    extras, selected, n = selected_members(kind, case, assigned_z, extra_members)
    return [
        'F is a finite simple SF4 family; empty sunflower cores are forbidden.',
        '|F| >= 68, d(x)=17, and the global maximum point degree is at most17; residual target51.',
        f'The complete root link is the recorded disjoint form {kind}.',
        'The universal I7 support reduction plus eight templates are imported, bound to the separate independent finite census of all77520 six-point candidates; I8/I9/I10 classification and the high-link split are also imported.',
        'H27, exact-anchor caps10/3/1, global incidence caps17/6/2, and the universal local43 structural lemmas are imported.',
        'Every actual anchor has closed neighbourhood at least 41 and each pair in it has degree sum at least 19.',
        ('All Y internals are absent under the separate D17 P10_001..012 component exclusion; this script records its receipts but does not independently replay those models.'
         if geometry(kind)['empty_y'] else 'All P9-side Y internals remain free; no P10 empty-internal premise is transferred to P9.'),
        'All Z internals remain free except the explicit branch restrictions below.',
        'Only for kind P9-Q8 with empty_z true, each Q8 triad point has global degree at most16: its complete pair-link with the root is C4, and every degree17 high-link template would force an actual Z-internal four-set. The three rows subtract their exact four prescribed root cones. This uses the high-link17 and I7/I8 classification, not any cap16 no-P9 theorem.',
        'Every explicitly selected extra residual four-set is an actual member. Selection does not assign any other internal membership. The represented universe is the union of the complete root core and selected actual members, with at most its one canonical extra point; every other exterior point remains unrepresented. Every fixed-member anchor, triangle, B4, sunflower-pruning and H27-witness test includes all selected actual members.',
        'C5/P5 costs and whole-component singleton lower bounds use the ordinary lemmas in D18-structural-tools.md and literal six-point-support checks.',
        'When s>=8 or d>=17 and k is7,8,9,10, the complete rooted point-link graph must occur in the classified intersecting I_k templates. All eight I7 templates are included; k7 alone is insufficient.',
        'The complete triangle-plus-path star lemma applies at each literal full seven-point hub, including H7: degree minus the three internal cover completions is at most15; singleton>=8 gives near size at most5 plus those completions.',
        'For every ordered pair of fixed actual members with exactly two common points, the universal B4 two-anchor triangle inequality s_m(R)+p_km(R)-1[(M minus h) union k is actual]<=12 is imposed for both shared m and both k in R minus M; root-companion membership and fixed-root offsets are exact.',
        'A literal pair of fixed actual members whose v-link triples are disjoint and both near an actual anchor forces its exact-v singleton count at most7 by B4. Named rows subtract exact root-star offsets; corresponding central local singleton states >=8 are pruned only under that same witness, with no mutation of cached catalogues.',
        'Y singleton-pool H27, cross15, affine and conditional rows apply to P10/P9. C5 pair rows use all partners; P5 pair rows separately exclude each vertex of its unique two-cover.',
        'The entire root-avoiding residual family with at most one Y point is intersecting: two disjoint members would admit a prescribed P9/P10 root cone avoiding their at-most-two-point combined Y trace, giving an empty-core sunflower. H27 bounds its full trace sum by27, with no root-cone offset and no exterior-support restriction.',
        'For a literal complete disjoint-support P9+K root link, every fixed actual Q outside x+Y has disjoint complement at most22 by the ordinary complete-link/HP15 lemma; at |F|>=68 its neighbourhood is at least46. Both rows use exact root-cone offsets, retain all surviving K cones, and require no Y-empty premise or support/classification bound on K.',
        'For each such fixed outside Q, the exact surviving K cones further sharpen the complement cap: k0 gives20, k>0 gives20+k, empty common intersection gives9+k, and singleton common intersection gives15+k by HP15 and the literal sunflower excluding simultaneous complementary exceptional traces. The minimum with22 is used; the corresponding neighbourhood bound is68 minus that cap. These local facts require only mu41/cap18, not cap16 no-P9.',
        'For every represented centre z outside x+Y in a P9 branch, the actual z-copies whose Y triples lie in H+B are bounded by6 via HP15 with the actual xH9 star; a separate row applies to H+C. Both centres are outside the tails. B and C are complementary and are never combined into one claimed intersecting tail family. All columns are full four-point traces and no root-cone offset applies.',
        'Small-complete-core H27 and guarded Z cross15/clique-H27 use the stated actual-member avoidance proofs; no universal whole-Z intersecting pool is assumed.',
        'Optional external H27 clique rows are hash-bound data: every trace pair including self is rechecked for a shared point or a declared fixed actual member disjoint from both. Fixed members must occur in this receiving branch and lie in the source represented universe plus the excluded root. Only same-universe transfer or root-cone-only lifting to one added actual marker is allowed; the latter aggregates every fine trace by restriction. Discovery weights and stored validation claims are ignored.',
        'Prior-art cross15, crowding26 and minimum used degree7 at mu41/cap<=18 are enabled and source-hash-bound to their ordinary bridges and prior replay receipts.',
        'The local43 call uses emin=17 and bootstrap parameters r10=r9=0; the prior μ41/cap18 minimum used degree7 is imported; no finite exterior support is assumed.',
        dict(case=case, actual_marker=marker_catalogue(kind)[case]['marker'],
             empty_z=bool(empty_z), assigned_z=None if assigned_z is None else list(assigned_z),
             forbidden=list(forbidden), forbid_four_core=bool(forbid_four_core),
             degree_distributions=bool(degree_distributions), crowding_imports=bool(crowding_imports),
             h27_cliques=h27_cliques, extra_members=list(extras),
             selected_actual_members=list(selected), represented_points=list(range(n))),
    ]


def run(kind, case='none', seconds=30, empty_z=False, assigned_z=None,
        forbidden=(), forbid_four_core=False, label=None, degree_distributions=False,
        crowding_imports=True, h27_cliques=None, h27_cliques_sha256=None,
        extra_members=()):
    """One explicitly requested numerical case; integer-box diagnostic only."""
    if not 0 < seconds <= 30:
        raise ValueError('Per-solver limit must be in (0,30] seconds')
    extras, selected, n = selected_members(kind, case, assigned_z, extra_members)
    _, clique_dependency = h27_clique_input(h27_cliques, h27_cliques_sha256)
    clique_hash = None if clique_dependency is None else clique_dependency['sha256']
    from scipy.optimize import linprog
    start = time.monotonic()
    tr, bounds, A, b, E, f, labels, sizes = build(
        kind, case, empty_z, assigned_z, forbidden, forbid_four_core,
        degree_distributions, crowding_imports, h27_cliques, clique_hash, extras)
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
                  h27_cliques=clique_dependency,
                  extra_members=list(extras), selected_actual_members=list(selected),
                  represented_points=list(range(n)),
                  status=int(result.status), message=result.message,
                  target_residuals=TARGET, root_degree=ROOT_DEGREE,
                  point_cap=POINT_CAP, mu=41, columns=len(bounds),
                  trace_columns=N, upper_rows=len(b), equal_rows=len(f),
                  catalogue_sizes=sizes, build_seconds=built_seconds,
                  solver_time_limit_seconds=seconds, seconds=time.monotonic() - start,
                  source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  imported_local43_sha256=hashlib.sha256(LOCAL43.read_bytes()).hexdigest(),
                  structural_note_sha256=hashlib.sha256((HERE / 'D18-structural-tools.md').read_bytes()).hexdigest(),
                  pool_note_sha256=hashlib.sha256((HERE / 'D18-pool-research.md').read_bytes()).hexdigest(),
                  literal_premises=premises(kind, case, empty_z, assigned_z, forbidden,
                                            forbid_four_core, degree_distributions, crowding_imports,
                                            clique_dependency, extras),
                  geometry=catalogue_metadata(kind),
                  assurance='Numerical discovery with an exact integer-box diagnostic of this conditional relaxation; not independent reconstruction, Lean, or a complete branch proof.')
    if crowding_imports:
        record['imported_crowding_sources'] = {
            name: dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            for name, path in CROWDING_SOURCES.items()}
    if geometry(kind)['empty_y']:
        record['P10_internal_exclusion_receipts'] = {}
        for number in range(1, 13):
            path = HERE / 'degree17' / f'P10_{number:03d}.json'
            old = json.loads(path.read_text())
            if (old['case']['component'] != 10 or old['case']['outside'] != 7
                    or old['root_degree'] != 17 or old['point_cap'] != 17
                    or old['mu'] != 41 or old['certificate']['G'] >= 0):
                raise ValueError('D17 P10-empty dependency receipt has wrong premises or gap')
            record['P10_internal_exclusion_receipts'][path.name] = dict(
                sha256=hashlib.sha256(path.read_bytes()).hexdigest(), recorded_gap=old['certificate']['G'],
                status='imported recorded exact gap; not independently replayed by this script')
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
                              below51=H + correction < TARGET * scale,
                              display=(H + correction) / scale,
                              inequality_sign='nonnegative weights on A*x<=b',
                              equality_sign='signed weights on E*x=f',
                              ineq=[[i, w, labels[i]] for i, w in enumerate(ys) if w],
                              eq=[[i, w] for i, w in enumerate(es) if w])
        record['primal_trace'] = [[s, float(value)] for s, value in zip(tr, result.x[:N]) if value > 1e-7]
    output = HERE / 'degree17_full'
    output.mkdir(exist_ok=True)
    if label is not None and (not label or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-' for c in label)):
        raise ValueError('Receipt label must be a simple filename stem')
    identity = dict(source_sha256=record['source_sha256'],
                    imported_local43_sha256=record['imported_local43_sha256'],
                    structural_note_sha256=record['structural_note_sha256'],
                    pool_note_sha256=record['pool_note_sha256'],
                    imported_crowding_sources=record.get('imported_crowding_sources', {}),
                    P10_internal_exclusion_receipts=record.get('P10_internal_exclusion_receipts', {}),
                    h27_cliques=clique_dependency,
                    extra_members=list(extras), selected_actual_members=list(selected),
                    represented_points=list(range(n)),
                    kind=kind, literal_premises=record['literal_premises'])
    fingerprint = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    record['premise_sha256'] = fingerprint
    stem = f'{kind}-{case}' + (f'-{label}' if label else '') + f'-{fingerprint[:12]}'
    destination = output / (stem + '.json')
    if destination.exists():
        raise FileExistsError(f'Refusing to overwrite an existing receipt: {destination}')
    # Bind the data actually used in build, not a changed file read after solve.
    _, final_clique_dependency = h27_clique_input(h27_cliques, clique_hash)
    if final_clique_dependency != clique_dependency:
        raise ValueError('H27 clique dependency changed during run')
    destination.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(dict(receipt=str(destination), status=record['status'],
                          upper=record.get('dual', {}).get('display'),
                          below51=record.get('dual', {}).get('below51'),
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
    ap.add_argument('--extra-members', default='[]',
                    help='JSON list of extra actual residual four-sets, each a mask or four-label list; leaves other memberships free')
    ap.add_argument('--forbid-four-core', action='store_true', help='Additional premise: every four-core residual is absent')
    ap.add_argument('--h27-cliques', type=pathlib.Path,
                    help='Optional discovery JSON of literal H27 cliques; revalidated against this actual branch')
    ap.add_argument('--h27-cliques-sha256',
                    help='Optional required input hash, for exact reconstruction or pinned discovery')
    ap.add_argument('--degree-distributions', action='store_true',
                    help='Optional stronger shared degree distributions; disabled by default')
    crowding = ap.add_mutually_exclusive_group()
    crowding.add_argument('--crowding-imports', dest='crowding_imports', action='store_true',
                          default=True, help='Use replayed prior-art cross15/crowding26 imports (default)')
    crowding.add_argument('--no-crowding-imports', dest='crowding_imports', action='store_false',
                          help='Disable prior-art cross15/crowding26 imports')
    ap.add_argument('--label')
    args = ap.parse_args()
    if args.h27_cliques_sha256 is not None and args.h27_cliques is None:
        ap.error('--h27-cliques-sha256 requires --h27-cliques')
    if args.h27_cliques is not None and not (args.solve or args.build_only):
        ap.error('--h27-cliques requires --build-only or --solve; catalogue output does not validate rows')
    if args.case not in marker_catalogue(args.kind):
        ap.error('Unknown marker case; request --catalogue first')
    assigned = None if args.assigned_z is None else json.loads(args.assigned_z)
    forbidden = json.loads(args.forbidden)
    extra_members = json.loads(args.extra_members)
    try:
        extras, selected, n = selected_members(args.kind, args.case, assigned, extra_members)
    except ValueError as error:
        ap.error(str(error))
    if extras and not (args.solve or args.build_only):
        ap.error('--extra-members requires --build-only or --solve; catalogue output does not validate actual branches')
    if not isinstance(forbidden, list) or any(type(v) is not int or v < 0 for v in forbidden):
        ap.error('--forbidden must be a JSON list of nonnegative integer masks')
    if assigned is not None and (not isinstance(assigned, list) or any(type(v) is not int or v < 0 for v in assigned)):
        ap.error('--assigned-z must be a JSON list of nonnegative integer masks')
    if args.solve:
        run(args.kind, args.case, args.seconds, args.empty_z, assigned,
            forbidden, args.forbid_four_core, args.label,
            args.degree_distributions, args.crowding_imports,
            args.h27_cliques, args.h27_cliques_sha256, extras)
    elif args.build_only:
        start = time.monotonic()
        _, clique_dependency = h27_clique_input(args.h27_cliques, args.h27_cliques_sha256)
        clique_hash = None if clique_dependency is None else clique_dependency['sha256']
        tr, bounds, A, b, E, f, labels, sizes = build(
            args.kind, args.case, args.empty_z, assigned, forbidden,
            args.forbid_four_core, args.degree_distributions, args.crowding_imports,
            args.h27_cliques, clique_hash, extras)
        _, final_dependency = h27_clique_input(args.h27_cliques, clique_hash)
        if final_dependency != clique_dependency:
            raise ValueError('H27 clique dependency changed during build')
        print(json.dumps(dict(kind=args.kind, case=args.case, traces=len(tr), columns=len(bounds),
                              upper_rows=len(b), equal_rows=len(f), catalogue_sizes=sizes,
                              extra_members=list(extras), selected_actual_members=list(selected),
                              represented_points=list(range(n)),
                              seconds=time.monotonic() - start,
                              literal_premises=premises(args.kind, args.case, args.empty_z, assigned,
                                                       forbidden, args.forbid_four_core,
                                                       args.degree_distributions,
                                                       args.crowding_imports,
                                                       clique_dependency, extras)), indent=2))
    else:
        print(json.dumps(catalogue_metadata(args.kind), indent=2))


if __name__ == '__main__':
    main()
