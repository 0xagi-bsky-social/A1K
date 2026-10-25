from pathlib import Path
import urllib.request,urllib.parse,json,datetime,concurrent.futures,re
out=Path(__file__).resolve().parent
queries={
'hal-title':'https://api.archives-ouvertes.fr/search/?'+urllib.parse.urlencode({'q':'title_t:sunflower','wt':'json','rows':'200','fl':'title_s,halId_s,uri_s,abstract_s,producedDate_s,submittedDate_s,version_i','sort':'submittedDate_tdate desc'}),
'hal-lemma':'https://api.archives-ouvertes.fr/search/?'+urllib.parse.urlencode({'q':'"sunflower lemma"','wt':'json','rows':'200','fl':'title_s,halId_s,uri_s,abstract_s,producedDate_s,submittedDate_s,version_i','sort':'submittedDate_tdate desc'}),
'hal-delta':'https://api.archives-ouvertes.fr/search/?'+urllib.parse.urlencode({'q':'"delta-system"','wt':'json','rows':'200','fl':'title_s,halId_s,uri_s,abstract_s,producedDate_s,submittedDate_s,version_i','sort':'submittedDate_tdate desc'}),
'rs-sunflower':'https://www.researchsquare.com/browse?'+urllib.parse.urlencode({'unified':'"sunflower lemma"'}),
'rs-sunflower-free':'https://www.researchsquare.com/browse?'+urllib.parse.urlencode({'unified':'"sunflower-free"'}),
'rs-delta-system':'https://www.researchsquare.com/browse?'+urllib.parse.urlencode({'unified':'"delta-system"'}),
'zenodo-mitchell-page':'https://zenodo.org/records/18248679'}
def fetch(item):
 name,url=item;r={'name':name,'url':url,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=25) as response:
   body=response.read();r.update(status=response.status,bytes=len(body));(out/(name+'.body')).write_bytes(body)
   if name.startswith('hal-'):
    data=json.loads(body);r['response']=data.get('response',data)
   if name.startswith('rs-'):
    m=re.search('<script id="__NEXT_DATA__" type="application/json">(.*?)</script>',body.decode(),re.S)
    if m:
     data=json.loads(m[1])['props']['pageProps'];r['pagePropsKeys']=list(data);r['initialProps']=data.get('initialProps')
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=7) as pool:result=list(pool.map(fetch,queries.items()))
(out/'native-refined.json').write_text(json.dumps(result,indent=2))
for r in result:
 if 'response' in r:print(r['name'],r['response'].get('numFound'),r['response'].get('docs'))
 else: print(json.dumps(r))

