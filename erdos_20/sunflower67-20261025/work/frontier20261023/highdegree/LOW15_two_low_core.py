#!/usr/bin/env python3
"""Tiny solver-free necessary core census for the three N45 two-low rows.

Exterior supports are derived from two high-root triangles and the low-low
pair residue (a two-edge path or triangle). No full-family support bound is
assumed. The extra necessary guard is proved in LOW15-two-low-core.md.
"""
import hashlib
import itertools as it
import json
import pathlib
import time


def edges(vertices):
    return tuple(frozenset(e) for e in it.combinations(sorted(vertices), 2))


def mask(points):
    return sum(1 << p for p in points)


def lift(ij, es):
    return [mask(ij) | mask(4 + x for x in e) for e in es]


def sunflower(ms):
    for i in range(len(ms)):
        a = ms[i]
        for j in range(i + 1, len(ms)):
            b = ms[j]
            ab = a & b
            for c in ms[j + 1:]:
                if ab == a & c == b & c:
                    return [a, b, c]
    return None


def fresh_canonical(points, base):
    new = sorted(set(points) - set(range(base)))
    return new == list(range(base, base + len(new)))


def serial_edges(es):
    return [sorted(e) for e in es]


def run():
    started = time.monotonic()
    A = frozenset(range(3))
    EA = edges(A)
    common = frozenset((0, 1))
    summaries = {}
    survivors = []
    for kind in ('highpair0-cross23', 'highpair1-cross13', 'highpair1-cross22'):
        stats = dict(base_assignments=0, sf_base_assignments=0,
                     guarded_completions=0, sf_completions=0)
        summaries[kind] = stats
        if kind == 'highpair0-cross23':
            configurations = []
            for k in range(4):
                for overlap in it.combinations(range(3), k):
                    B = frozenset(overlap) | frozenset(range(3, 6 - k))
                    for E13 in it.combinations(edges(B), 2):
                        configurations.append((B, (), (EA[0], EA[1]), EA,
                                               edges(B), E13))
        else:
            configurations = []
            for B in (A, frozenset((0, 1, 3))):
                EB = edges(B)
                if kind == 'highpair1-cross13':
                    for a in EA:
                        for b in EB:
                            if a != common and b != common:
                                configurations.append((B, (common,), (a,), EA,
                                                       EB, (b,)))
                else:
                    for E02, E03 in it.product(it.combinations(EA, 2), repeat=2):
                        if common in E02 and common in E03:
                            continue
                        for E12, E13 in it.product(it.combinations(EB, 2), repeat=2):
                            if common in E12 and common in E13:
                                continue
                            configurations.append((B, (common,), E02, E03,
                                                   E12, E13))
        for B, E01, E02, E03, E12, E13 in configurations:
            stats['base_assignments'] += 1
            base_ms = [15]
            for ij, es in (((0, 1), E01), ((0, 2), E02), ((0, 3), E03),
                           ((1, 2), E12), ((1, 3), E13)):
                base_ms.extend(lift(ij, es))
            if sunflower(base_ms):
                continue
            stats['sf_base_assignments'] += 1
            base = max(A | B) + 1
            for C in it.combinations(range(base + 3), 3):
                if not fresh_canonical(C, base):
                    continue
                if kind == 'highpair0-cross23':
                    candidates = list(it.combinations(edges(C), 2))
                else:
                    # Each edge must meet each high P9 support, whose support
                    # avoids A or B. A triangle thus uses <=1 vertex of each.
                    if len(set(C) & A) > 1 or len(set(C) & B) > 1:
                        continue
                    candidates = [edges(C)]
                for E23 in candidates:
                    if any(e <= A or e <= B for e in E23):
                        continue
                    stats['guarded_completions'] += 1
                    ms = base_ms + lift((2, 3), E23)
                    if sunflower(ms):
                        continue
                    stats['sf_completions'] += 1
                    survivors.append(dict(kind=kind, A=sorted(A), B=sorted(B),
                        E01=serial_edges(E01), E02=serial_edges(E02),
                        E03=serial_edges(E03), E12=serial_edges(E12),
                        E13=serial_edges(E13), E23=serial_edges(E23),
                        actual_core_masks=ms))
                if time.monotonic() - started > 0.9:
                    raise RuntimeError('Bounded diagnostic exceeded 0.9 seconds; no result saved')
    return dict(schema='cap15-N45-two-low-core-necessary-census-v1',
        scope='finite necessary actual-core geometry only; arbitrary exterior full-family support',
        complete=True, source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        premises=['cap15', 'size68', 'mu41', 'N<=45', 'no-P10',
                  'B4 at singleton9 roots', 'P9 isolation',
                  'intersecting P9 plus <=1 extra-link triple has size<=21',
                  'every low-low residue edge meets both high P9 supports'],
        summaries=summaries, survivors=survivors,
        seconds=time.monotonic() - started)


if __name__ == '__main__':
    data = run()
    output = pathlib.Path(__file__).with_name('LOW15-two-low-core-census.json')
    output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k: data[k] for k in ('complete', 'summaries', 'seconds')}))
