from pathlib import Path
import hashlib,json
root=Path('/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob/work/frontier20261023')
r=root/'review67';out={}
payload=(r/'checks/round05/citation_verifier/root_tree_payload.bin').read_bytes()
wrapper=json.loads((r/'checks/round09/citation_verifier/h27-commit-response.json').read_text())
commit=json.loads(wrapper['result']['structuredContent']['content'])
actual=hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()
out['identifier_relationship']={'payload_bytes':len(payload),'payload_sha256':hashlib.sha256(payload).hexdigest(),'reconstructed_tree':actual,'returned_commit':commit['sha'],'returned_tree':commit['commit']['tree']['sha'],'tree_matches':actual==commit['commit']['tree']['sha'],'commit_differs_from_tree':commit['sha']!=actual,'scope':'Saved response and existing tree bytes only; no new fetch or historical computation.'}
# Test the actual-anchor sign/offset formulation throughout all possible
# integer offsets for complete root stars of sizes17,18,19.
results=[]
for root_degree in (17,18,19):
 comparisons=0;disagreements=0;strictly_above_41=0
 for base in range(root_degree+1):
  for residual_meeting in range(69-root_degree):
   row=(-residual_meeting<=base-41)
   meaning=(base+residual_meeting>=41)
   comparisons+=1;disagreements+=row!=meaning
   strictly_above_41+=row and base+residual_meeting>41
 results.append({'root_degree':root_degree,'tests':comparisons,'disagreements':disagreements,'accepted_above_41':strictly_above_41})
out['lower_bound_offset_controls']=results
h=json.loads((r/'public/round10/prior-committed-history.json').read_text())
rows=[];required=[];resolutions={};mismatches=[]
for number,round_ in enumerate(h['rounds'],1):
 for wrapped in round_['submissions']:
  c=wrapped['content'];p=wrapped['provenance'];rows.append(c)
  if json.loads(p['public_response'])!=c:mismatches.append((number,c['role'],'response_content'))
  if hashlib.sha256(p['public_response'].encode()).hexdigest()!=p['response_sha256']:mismatches.append((number,c['role'],'response_hash'))
  for j,_ in enumerate(c['required_revisions'],1):required.append((f"{c['agent_id']}:round-{number}:required-revision-{j}",c['agent_id'],number))
  for v in c['revisions']:
   if v['status']=='resolved':resolutions.setdefault(v['finding_id'],[]).append((c['agent_id'],number))
unclosed=[key for key,agent,round_ in required if not any(a==agent and n>round_ for a,n in resolutions.get(key,[]))]
out['committed_obligations']={'rounds':len(h['rounds']),'submissions':len(rows),'distinct_contexts':len({c['context_id'] for c in rows}),'each_round_12_distinct_roles':all(len(rr['submissions'])==12 and len({x['content']['role'] for x in rr['submissions']})==12 for rr in h['rounds']),'required_revision_items':len(required),'without_later_original_reviewer_resolution':unclosed,'response_content_or_hash_mismatches':mismatches,'own_required_revisions':sum(len(c['required_revisions']) for c in rows if c['role']=='data_analyst'),'scope':'Committed rounds1-9 only; current round and separate final audits are not counted.'}
Path('/tmp/r67_data_round10/checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
