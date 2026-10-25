from pathlib import Path
from fractions import Fraction
from html.parser import HTMLParser
from math import comb
import hashlib,json
root=Path('/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob/work/frontier20261023')
archives=root/'literature/refresh20261025/archives'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
out={}
f=3*Fraction(863,432)**8
out['comparison_arithmetic']={'binomial_7_4':comb(7,4),'binomial_8_4':comb(8,4),'support_bound_at_8':str(f),'strictly_above_760':f>760,'support_base_above_one':Fraction(863,432)>1,'vector_coefficient':6**4,'vc_uniform_bound':(50*4*3)**4,'shifted_recurrence_bound':2*2*3**4,'maximum_67_forcing_68':67+1,'maximum_68_forcing_69':68+1}
h=json.loads((archives/'hal-all-title.json').read_text())['response'];docs=h['docs']
manifest=json.loads((archives/'artifact-manifest.json').read_text())
arch_checks={x['path']:sha(archives/x['path'])==x['sha256'] for x in manifest['files']}
out['archive_integrity']={'files':len(arch_checks),'mismatches':[k for k,v in arch_checks.items() if not v]}
out['hal']={'reported':h['numFound'],'start':h['start'],'numFoundExact':h['numFoundExact'],'actual':len(docs),'unique_uri':len({d['uri_s'] for d in docs}),'unique_hal_id':len({d['halId_s'] for d in docs}),'missing_title':sum(not d.get('title_s') for d in docs),'scope':'Only saved title_t:sunflower* response; no fulltext or external completeness verification.'}
class Scripts(HTMLParser):
 def __init__(self): super().__init__();self.capture=False;self.data=[]
 def handle_starttag(self,t,a):
  if t=='script' and dict(a).get('id')=='__NEXT_DATA__':self.capture=True
 def handle_endtag(self,t):
  if t=='script':self.capture=False
 def handle_data(self,d):
  if self.capture:self.data.append(d)
rs=[]
for fn in ['rs-sunflower.body','rs-sunflower-free.body','rs-delta-system.body']:
 p=Scripts();p.feed((archives/fn).read_text());d=json.loads(''.join(p.data));r=d['props']['pageProps']['initialProps']['result'];rs.append({'file':fn,'query':d['query'],'retrieved':len(r['data']),'metadata':{k:v for k,v in r.items() if k!='data'}})
out['researchsquare']=rs
review=root/'review67'
p8=review/'public/round08';p9=review/'public/round09'
m8=(p8/'manuscript.md').read_text();m9=(p9/'manuscript.md').read_text()
s8=json.loads((p8/'snapshot.json').read_text());s9=json.loads((p9/'snapshot.json').read_text());before={e['id']:e for e in s8['evidence']};after={e['id']:e for e in s9['evidence']}
out['scope_immutability']={'sections_3_onward_byte_identical':m8.split('## 3.',1)[1]==m9.split('## 3.',1)[1],'previous_evidence_entries':len(before),'all_previous_entries_unchanged':all(after.get(k)==v for k,v in before.items())}
manifest=json.loads((review/'checks/round05/data_analyst/archive-manifest.json').read_text());ok=[sha(x['archive'])==x['sha256'] for x in manifest['files']]
b=json.loads((review/'checks/round05/data_analyst/baseline.json').read_text());neg=json.loads((review/'checks/round05/data_analyst/negative-multiplier-replay.json').read_text())
deps=list(b['dependencies'].values())+[b['source']]
bound=[(x['path'],sha(x['path'])==x['sha256']) for x in deps]
x=b['exact_replay']
out['prior_fresh_replay_preservation']={'archived_files':len(ok),'all_archive_hashes_match':all(ok),'dependencies_and_source':len(bound),'mismatches':[p for p,ok in bound if not ok],'receipt_unchanged':sha(b['receipt_path'])==b['receipt_sha256'],'replayer_unchanged':sha(root/'highdegree/replay_degree18_p10.py')==b['replayer_sha256'],'baseline_result':b['result'],'exact_replay':x,'negative_result':neg['result'],'negative_error':neg.get('error'),'scope':'Preservation and exact saved arithmetic only; neither replay rerun.'}
out['prior_fresh_replay_preservation']['saved_integer_identities_match']=(x['H']+x['correction']==x['upper_numerator'] and x['upper_numerator']<x['target_numerator'] and Fraction(x['upper_numerator'],x['scale'])==Fraction(*x['reduced_upper']))
Path('/tmp/r67_data_round09/checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
