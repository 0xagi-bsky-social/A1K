"""Freeze actual current author inputs after the preceding full round commits.

This helper neither schedules reviewers nor creates review judgments.
"""
import hashlib
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore

BASE = Path(__file__).resolve().parent
FOCUS = {
    2: 'Source map, prior work and gaps. Trace the stated imports to their actual sources, compare theorem scope and conventions, and test the new obligation map. Recheck your own prior requested revisions explicitly.',
    3: 'Theory, mechanisms, rival explanations and counterexamples. Actively test hidden support assumptions, alternative configurations, quantifiers, and family-to-model implications; identify a concrete counterexample if any.',
    4: 'Methods and proof obligations. Audit the acyclic import order, exhaustive case reductions, finite domain completeness, guarded uses and software trust boundaries. Check research attribution and integrity.',
    5: 'Calculations, robustness and reproducibility. Inspect or reproduce exact scalar identities, finite coverage, certificate/replay bindings and tested corruption controls. Arrange any heavy replay centrally before execution.',
    6: 'Integrated manuscript. Read the whole proof as a coherent argument, verify every bridge is exposed or precisely located, and check consistency among statement, evidence and limitations.',
    7: 'Skeptical review. Every role scrutinizes the strongest potential objections and failure modes, including committed Alpha findings. Challenge assumptions rather than treating prior acceptance as evidence.',
    8: 'Constructive review. Every role tests the proposed repairs and alternative formulations, including committed Beta findings. Verify genuine resolution of objections and useful claim limits.',
    9: 'Revision and final fact/citation/logic/method/data/text-reuse audit. Check outstanding findings, retained caveats, source identities and immutable mathematical evidence. Report any remaining necessary change.',
    10: 'Same-version final review and lock. Inspect the exact final bytes and all committed history, confirm or challenge resolution of every material objection, and decide whether the manuscript is ready for the separate final audits.',
}

def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False)+'\n')

def main():
    store = NativeRunStore(BASE/'run')
    history = store.bundle()  # Fails if a round is still pending.
    number = len(history['rounds'])+1
    dest = BASE/'public'/f'round{number:02d}'
    if dest.exists():
        raise FileExistsError(dest)
    dest.mkdir()
    if number == 2:
        shutil.copyfile(BASE/'author-response-r1.md', dest/'author-response.md')
    elif (BASE/f'author-response-r{number-1}.md').exists():
        shutil.copyfile(BASE/f'author-response-r{number-1}.md', dest/'author-response.md')
    write_json(dest/'prior-committed-history.json', history)
    # An index of actual committed findings, not replacement votes or judgments.
    finding_index = []
    for row in history['rounds']:
        for submission in row['submissions']:
            content = submission['content']
            finding_index.append({
                'round': content['round'], 'agent_id': content['agent_id'],
                'role': content['role'], 'decision': content['decision'],
                'findings': content['findings'], 'revisions': content['revisions'],
                'required_revisions': [
                    {'id': f"{content['agent_id']}:round-{content['round']}:required-revision-{i+1}", 'text': text}
                    for i, text in enumerate(content['required_revisions'])]
            })
    write_json(dest/'prior-findings-index.json', finding_index)
    state = {
        'frontier_gate': str(BASE/'FRONTIER_GATE.json'),
        'frontier_gate_refresh': str(BASE/'FRONTIER_GATE_REFRESH_20261025.json'),
        'prospective_contract_amendment': str(BASE/'CONTRACT_AMENDMENT_20261025.json'),
        'phase_focus': FOCUS.get(number, 'Further substantive revision and same-version review as required.'),
        'round_history': str(dest/'prior-committed-history.json'),
        'revision_response': str(BASE/'public'/'round02'/'author-response.md'),
        'revision_response_sha256': hashlib.sha256((BASE/'public'/'round02'/'author-response.md').read_bytes()).hexdigest(),
        'author_response_history': [
            {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in sorted((BASE/'public').glob('round*/author-response.md'))],
        'review_boundary': 'Read only frozen common inputs, cited evidence, your own prior responses, and the supplied committed history. Do not inspect current pending journal or peers\' incoming files. Heavy jobs require central scheduling.',
        'manuscript_status': 'Ordinary computer-assisted theorem under actual autonomous agent review; no final acceptance or end-to-end Lean claim.'
    }
    for name in ('manuscript.md', 'contract.json', 'roster.json'):
        shutil.copyfile(BASE/name, dest/name)
    result = store.open_round((dest/'manuscript.md').read_bytes(),
        json.loads((BASE/'evidence.json').read_text()),
        json.loads((BASE/'verification.json').read_text()), state)
    write_json(dest/'snapshot.json', result['snapshot'])
    write_json(dest/'bindings.json', {k:v for k,v in result.items() if k!='snapshot'})
    (dest/'assignment.md').write_text(f'''# Actual round {number} assignment

Use your existing roster identity and specialist mandate. Read {BASE/'REVIEW_PROTOCOL.md'} and the immutable manuscript, snapshot, contract and roster in this directory.

Expected manuscript SHA256: {result['snapshot']['manuscript_sha256']}
Expected canonical snapshot SHA256: {result['snapshot_sha256']}

Phase: {state['phase_focus']}

Committed history is in prior-committed-history.json. The faithful prior-findings-index.json helps locate earlier objections, but does not replace actual source checks. Author responses are listed and hash-bound in snapshot.public_state.author_response_history; they are proposals for resolution, not reviewer decisions. Explicitly close your own previously requested revisions only when actually satisfied, using their exact IDs.

Perform at least three substantive checks with specific locators and clearly bounded coverage. Preserve independent judgment; report any counterexample or uncovered premise. At this phase, pursue your domain-specific concerns rather than repeat earlier hash checks as your entire analysis. Bounded standard-library checks and source reads are allowed; ask root to schedule heavy jobs. Do not read current incoming peers or the pending run journal.

Save your actual JSON to {BASE/'incoming'/f'round{number:02d}'}/YOUR_NATIVE_ROLE.json and return the same JSON in your final response. All required protocol fields must be present. Keep summaries concise, recording concrete observations and honest limits. No manuscript edits or final-publication claim.
''')
    (BASE/'incoming'/f'round{number:02d}').mkdir(exist_ok=True)
    print(json.dumps({'round': number, 'directory': str(dest),
        'snapshot_sha256': result['snapshot_sha256'],
        'manuscript_sha256': result['snapshot']['manuscript_sha256']}, ensure_ascii=False))

if __name__ == '__main__':
    main()
