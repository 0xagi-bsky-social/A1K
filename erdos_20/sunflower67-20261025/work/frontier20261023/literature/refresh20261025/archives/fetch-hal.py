from pathlib import Path
import urllib.request,urllib.parse,json,datetime,concurrent.futures,re
out=Path(__file__).resolve().parent
qs={'hal-all-title':'title_t:sunflower*','hal-free':'"sunflower-free"','hal-conjecture':'"sunflower conjecture"','hal-delta-math':'"delta-system" AND (mathematics OR combinatorics OR sets)','hal-tournesol':'tournesol AND (combinatoire OR conjecture)'}
def fetch(item):
 name,q=item
 url='https://api.archives-ouvertes.fr/search/?'+urllib.parse.urlencode({'q':q,'wt':'json','rows':'2000','fl':'title_s,halId_s,uri_s,abstract_s,producedDate_s,submittedDate_s,version_i,domain_s,primaryDomain_s','sort':'submittedDate_tdate desc'})
 r={'name':name,'q':q,'url':url,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=25) as response:
   body=response.read();(out/(name+'.json')).write_bytes(body);r['status']=response.status
   data=json.loads(body)['response'];r.update(total=data['numFound'],retrieved=len(data['docs']))
   candidates=[]
   for d in data['docs']:
    if name!='hal-all-title' or any(x.split('.')[0] in ['math','info'] for x in d.get('domain_s',[])) or re.search('famil|conjecture|lemma|hypergraph|combinator|bound|sunflower.free|sets', ' '.join(d.get('title_s',[])),re.I):
     candidates.append(d)
   r['candidate_documents']=candidates
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as p:result=list(p.map(fetch,qs.items()))
(out/'hal-final-searches.json').write_text(json.dumps(result,indent=2))
for r in result:
 print(r['name'],r.get('total'),r.get('retrieved'),r.get('error'))
 for d in r.get('candidate_documents',[]):print(d['uri_s'], d.get('submittedDate_s'),' | '.join(d.get('title_s',[])),d.get('domain_s'))

