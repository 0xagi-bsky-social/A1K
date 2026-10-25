from pathlib import Path
import urllib.request, urllib.parse, json, datetime, concurrent.futures
out=Path(__file__).resolve().parent
urls={
'hal-native-escalated':'https://api.archives-ouvertes.fr/search/?'+urllib.parse.urlencode({'q':'sunflower OR "delta-system"','fq':'domain_s:math*','wt':'json','rows':'200','fl':'title_s,halId_s,uri_s,abstract_s,producedDate_s,submittedDate_s,version_i','sort':'submittedDate_tdate desc'}),
'zenodo-native-escalated':'https://zenodo.org/api/records?'+urllib.parse.urlencode({'q':'"sunflower lemma" OR "sunflower conjecture" OR "sunflower-free"','size':'100','sort':'mostrecent'}),
'zenodo-mitchell-api':'https://zenodo.org/api/records/18248679',
'osf-native-escalated':'https://osf.io/preprints/discover?q=sunflower',
'preprints-native-escalated':'https://www.preprints.org/search?search1=sunflower',
'vixra-primary-escalated':'https://ai.vixra.org/abs/2601.0054',
'mathoa-home-escalated':'https://www.mathoa.org/about/',
'researchsquare-native-escalated':'https://www.researchsquare.com/browse?term=sunflower',
'techrxiv-native-escalated':'https://www.techrxiv.org/search?query=sunflower',
'ssrn-primary-escalated':'https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6913500'}
def fetch(item):
 name,url=item
 result={'name':name,'url':url,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
  with urllib.request.urlopen(req,timeout=25) as r:
   body=r.read(); result.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'),bytes=len(body));(out/(name+'.body')).write_bytes(body)
 except Exception as e:result['error']=str(e)
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool: results=list(pool.map(fetch,urls.items()))
(out/'native-http-escalated.json').write_text(json.dumps(results,indent=2))
print(json.dumps(results,indent=2))

