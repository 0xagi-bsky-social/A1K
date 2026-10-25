from pathlib import Path
import sys, json, shutil, hashlib
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
def dump(p,v): p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.now(timezone.utc).isoformat()
contract={
 'run_id':'frontier20261019-native-review',
 'topic':'Finite support reduction and near-extremal completion in sunflower-free families',
 'question':'Which universe-independent support and near-extremal completion claims follow from the pinned A1K development, new elementary arguments, and locally checked Lean roots, with all remaining exclusion and formalization obligations explicit?',
 'mode':'theoretical','field':'Extremal set theory and formal verification',
 'acceptance_criteria':'Correct quantified mathematical arguments, accurate source attribution, explicit distinction of paper proof, checked roots and diagnostic computation, no unresolved material issue, twelve isolated role contexts across ten synchronous substantive rounds and final Chief/Alpha/Beta same-byte acceptance.',
 'created_at':now,'evidence_cutoff':now,
 'constraints':['No global originality claim','No I27/profile exclusion or all-rank conjecture claim','No independent human certification','No public hosting or journal submission','No clean mathlib rebuild claim'],
 'assumptions':['Finite distinct uniform families; three distinct petals and empty core included','Reflexive intersection interface; equivalent to ordinary intersectingness for positive rank','Existing cached dependency objects from pinned source revisions'],
 'audience':'Researchers in extremal combinatorics and proof assistants',
 'timezone':'America/New_York','citation_style':'Numbered primary-source references with immutable versions and theorem locators',
 'methods':['Mathematical double counting and classification','Exact integer diagnostics','Lean elaboration and axiom print receipts','Bounded local source comparison','Twelve-role synchronous native review'],
 'inclusion':'Pinned A1K and OpenAI mathematical snapshots, directly accessed primary literature, actual local proof and computation artifacts',
 'exclusion':'Unperformed search conclusions, unaudited whole-module promotion, unsupported novelty or independence assertions',
 'budget':'Ten complete rounds, then final audits; additional rounds if needed and runtime allows. Reviewers use concise substantive checks; no optional service provisioning.',
 'deliverables':['report.md','report.html','report.pdf','Separate machine evidence and review bundle'],
 'prospective_amendments':[]
}
dump(ROOT/'contract.json',contract)
files=[
 ('E01','lean/SupportBound.lean','Local Lean source for universal support inequality, support72 and finite-obstruction equivalence','limited',['Locally compiled against retained dependency objects; source is not an independent verification']),
 ('E02','logs/SupportBound.json','Actual compiler output for six printed SupportBound roots','limited',['Printed root axioms and exit status are local compiler evidence, not clean dependency rebuild']),
 ('E03','lean/SupportGrid.lean','Finite support56 numerical grid source','available',[]),
 ('E04','logs/SupportGrid.json','Actual exit-zero SupportGrid compiler receipt','limited',['Grid leaf and wrapper only; no full support56 structural assembly']),
 ('E05','lean/Support56.lean','Universal three-star second-moment Lean source','limited',['Does not finish support56 assembly']),
 ('E06','logs/Support56.json','Exit-zero stable-source receipt for universal second-moment root','limited',['Retained dependency object trust; printed roots scope only']),
 ('E07','structural/support56-draft.md','Elementary support56 mathematical argument','limited',['Universal Lean assembly not complete']),
 ('E08','profile/nine-classification-proof.txt','Elementary nine-triple classification and completion proof','limited',['Universal Lean assembly not complete']),
 ('E09','profile/ProfileNine.lean','Trace arithmetic formalization','limited',['Arithmetic ledger is not full classification']),
 ('E10','profile/ProfileNine.receipt.json','Exit-zero two-root trace ledger compiler receipt','limited',['No universal completion theorem established by this receipt']),
 ('E11','profile/independent-support56-grid.json','Separately computed exact finite-grid diagnostic','limited',['Ordinary Python diagnostic; no formal semantic bridge']),
 ('E12','profile/nine-diagnostic-results.json','Exact local nine-triple finite diagnostics','limited',['Finite support enumeration does not prove arbitrary-support classification']),
 ('E13','search/profile_a_result.json','Failed Profile A model-building attempt','limited',['Solver not called; no SAT/UNSAT conclusion']),
 ('E14','runtime.json','Observed Lean runtime and pinned dependency revision comparison','limited',['Revision comparison does not authenticate object bytes']),
 ('E15','cache-source-comparison.json','155 pinned source files compare without mismatch','limited',['Matching source does not authenticate compiled cache']),
]
evidence=[]
for ident,rel,desc,status,limits in files:
 src=BASE/rel; dst=ROOT/'evidence'/ident/src.name; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,dst)
 evidence.append({'id':ident,'kind':'local-artifact','description':desc,'locator':str(dst),'method':'Read and copied actual local bytes before opening first review snapshot','status':status,'limitations':limits,'content_sha256':digest(dst)})
for ident,name,desc in [('E16','primary-web-initial.json','Actual web tool returned primary source text, including bibliographic metadata'),('E17','primary-web-targeted.json','Actual web tool targeted arXiv 6.3/8 and A1K finite-reduction passages')]:
 p=ROOT/'evidence'/name
 evidence.append({'id':ident,'kind':'primary-web-tool-output','description':desc,'locator':str(p),'method':'web.run open/find on 2026-10-19','status':'limited','limitations':['Tool-returned representation, not authenticated full HTTP bytes; bounded retrieval and no exhaustive literature coverage'],'content_sha256':digest(p)})
dump(ROOT/'evidence.json',evidence)
verification=[]
for scope in ['facts','citations','logic','methodology','data','text_reuse']:
 verification.append({'scope':scope,'status':'limited' if scope!='text_reuse' else 'not-run','method':'Initial coordinator comparison of actual local artifacts and primary retrieved text; specialist checks pending' if scope!='text_reuse' else 'Bounded local comparison assigned to copyeditor in review; not yet run','observations':['Initial draft qualifications align checked roots with compiler receipts; full scholarly review pending'] if scope!='text_reuse' else ['No corpus-wide originality service used'],'limitations':['Initial check is bounded; autonomous agent review is not independent certification'] if scope!='text_reuse' else ['No broad originality or plagiarism-free certificate supported'],'evidence_ids':['E01','E02','E05','E06','E16','E17'] if scope!='text_reuse' else []})
dump(ROOT/'verification.json',verification)
print(json.dumps({'evidence_count':len(evidence),'cutoff':now},indent=2))
