"""Bounded Markdown/ReportLab renderer with explicit reviewed formula mappings.

The native publisher remains the review and byte-integrity gate. Six displayed
formulas are mapped explicitly; unsupported formulas fail rather than guessing.
"""
from pathlib import Path
import html,json,sys,subprocess,tempfile,hashlib,re
RUNTIME='/home/user/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3'
FORMULAS={
 r'D n + m(m+r-1) \leq (D+1)rm': '<i>D n</i> + <i>m</i>(<i>m+r</i>−1) ≤ (<i>D</i>+1)<i>r m</i>.',
 r'\sum_x d(x)^2 \geq m(m+r-1)': '∑<sub>x</sub> <i>d</i>(<i>x</i>)<super>2</super> ≥ <i>m</i>(<i>m+r</i>−1).',
 r'd(x)^2+D\leq(D+1)d(x)': '<i>d</i>(<i>x</i>)<super>2</super> + <i>D</i> ≤ (<i>D</i>+1)<i>d</i>(<i>x</i>).',
 r'I(27)\ \Longleftrightarrow\ \text{there is no intersecting 28-member, rank-four, three-sunflower-free family on Fin 72}': '<i>I</i>(27) ⟺ there is no intersecting 28-member, rank-four, three-sunflower-free family on Fin 72.',
 r'\sum_v d(v)^2 \geq m(m+r-1)+x(x-1)+y(y-1)+z(z-1)-t(t-1)': '∑<sub>v</sub> <i>d</i>(<i>v</i>)<super>2</super> ≥ <i>m</i>(<i>m+r</i>−1) + <i>x</i>(<i>x</i>−1) + <i>y</i>(<i>y</i>−1) + <i>z</i>(<i>z</i>−1) − <i>t</i>(<i>t</i>−1).',
 r'|I|-1\geq \binom{j}{2}-\binom{j}{3}': '|<i>I</i>| − 1 ≥ binom(<i>j</i>,2) − binom(<i>j</i>,3).',
}
def inline(children):
 out=[]
 for t in children or []:
  if t.type=='text':out.append(html.escape(t.content))
  elif t.type=='code_inline':out.append('<font name="ReviewMono" size="8">'+html.escape(t.content)+'</font>')
  elif t.type in ['softbreak','hardbreak']:out.append(' ' if t.type=='softbreak' else '<br/>')
  elif t.type=='strong_open':out.append('<b>')
  elif t.type=='strong_close':out.append('</b>')
  elif t.type=='em_open':out.append('<i>')
  elif t.type=='em_close':out.append('</i>')
  elif t.type=='link_open':out.append('<link href="'+html.escape(t.attrGet('href'),quote=True)+'" color="#244d77">')
  elif t.type=='link_close':out.append('</link>')
  else:raise ValueError('Unsupported inline token: '+t.type)
 return ''.join(out)
def blocks(manuscript):
 from markdown_it import MarkdownIt
 md=MarkdownIt('commonmark',{'html':False});md.enable('table')
 ts=md.parse(manuscript.decode());result=[];i=0
 while i<len(ts):
  t=ts[i]
  if t.type=='heading_open':result.append({'type':'heading','level':int(t.tag[1:]),'text':inline(ts[i+1].children)});i+=3
  elif t.type=='paragraph_open':
   p=ts[i+1];match=re.fullmatch(r'\$\$(.*?)\$\$',p.content,re.S)
   if match:
    exact=match.group(1);key=exact.removesuffix(r'\text{.}')
    if key==exact or key not in FORMULAS:raise ValueError('Unsupported display formula '+exact)
    result.append({'type':'math','text':FORMULAS[key],'source':exact})
   else:result.append({'type':'paragraph','text':inline(p.children)})
   i+=3
  elif t.type in ['code_block','fence']:
   result.append({'type':'code','text':t.content.rstrip('\n')});i+=1
  elif t.type=='table_open':
   rows=[];row=[];i+=1
   while ts[i].type!='table_close':
    q=ts[i]
    if q.type=='tr_open':row=[]
    elif q.type=='inline':row.append(inline(q.children))
    elif q.type=='tr_close':rows.append(row)
    i+=1
   result.append({'type':'table','rows':rows});i+=1
  else:raise ValueError('Unsupported block token: '+t.type)
 return result

def write_pdf(payload,title,destination):
 from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
 from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,KeepTogether,Table,TableStyle
 from reportlab.lib.pagesizes import letter
 from reportlab.lib import colors
 from reportlab.pdfbase import pdfmetrics
 from reportlab.pdfbase.ttfonts import TTFont
 fonts=Path('/usr/share/fonts/truetype/dejavu')
 for name,file in [('ReviewSerif','DejaVuSerif.ttf'),('ReviewSerif-Bold','DejaVuSerif-Bold.ttf'),('ReviewSerif-Italic','DejaVuSerif-Italic.ttf'),('ReviewSerif-BoldItalic','DejaVuSerif-BoldItalic.ttf'),('ReviewSans','DejaVuSans.ttf'),('ReviewMono','DejaVuSansMono.ttf')]:pdfmetrics.registerFont(TTFont(name,str(fonts/file)))
 pdfmetrics.registerFontFamily('ReviewSerif',normal='ReviewSerif',bold='ReviewSerif-Bold',italic='ReviewSerif-Italic',boldItalic='ReviewSerif-BoldItalic')
 styles=getSampleStyleSheet()
 for st in styles.byName.values():st.fontName='ReviewSerif'
 styles['BodyText'].fontSize=9.5;styles['BodyText'].leading=13.2;styles['BodyText'].spaceAfter=6
 styles['Title'].fontName='ReviewSans';styles['Title'].fontSize=22;styles['Title'].leading=27;styles['Title'].spaceAfter=18
 styles['Heading2'].fontName='ReviewSans';styles['Heading2'].fontSize=13;styles['Heading2'].leading=17;styles['Heading2'].spaceBefore=14;styles['Heading2'].spaceAfter=8;styles['Heading2'].keepWithNext=True
 styles['Heading3'].fontName='ReviewSans';styles['Heading3'].fontSize=11;styles['Heading3'].leading=14
 math=ParagraphStyle('Math',parent=styles['BodyText'],fontSize=10,leading=15,leftIndent=10,spaceBefore=4,spaceAfter=9)
 code=ParagraphStyle('Code',parent=styles['BodyText'],fontName='ReviewMono',fontSize=8,leading=11,leftIndent=10,spaceBefore=4,spaceAfter=8)
 cell=ParagraphStyle('Cell',parent=styles['BodyText'],fontSize=8.4,leading=11,spaceAfter=0)
 story=[]
 for b in payload:
  if b['type']=='heading':story.append(Paragraph(b['text'],styles['Title'] if b['level']==1 else styles['Heading2'] if b['level']==2 else styles['Heading3']))
  elif b['type']=='paragraph':story.append(KeepTogether([Paragraph(b['text'],styles['BodyText'])]))
  elif b['type']=='math':story.append(KeepTogether([Paragraph(b['text'],math)]))
  elif b['type']=='code':
   # Preserve source notation while making its block structure legible.
   text='<br/>'.join(html.escape(x).replace(' ','&#160;') for x in b['text'].splitlines())
   story.append(KeepTogether([Paragraph(text,code)]))
  elif b['type']=='table':
   rows=[[Paragraph(c,cell) for c in row] for row in b['rows']]
   table=Table(rows,colWidths=[206,304],repeatRows=1,hAlign='LEFT')
   table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#edf3fa')),('GRID',(0,0),(-1,-1),.4,colors.HexColor('#b5c2d1')),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),6)]))
   story.extend([table,Spacer(1,8)])
 note='A1K Agentic SuperResearch · Local automated publication. Review records and artifact hashes describe checks performed locally; they do not establish external authentication, statistical reviewer independence, or independent human certification.'
 story.append(KeepTogether([Spacer(1,12),Paragraph(html.escape(note),styles['BodyText'])]))
 def footer(canvas,doc):
  canvas.saveState();canvas.setFont('Helvetica',7);canvas.setFillColorRGB(.3,.35,.42);canvas.drawCentredString(letter[0]/2,25,'A1K Agentic SuperResearch | '+str(doc.page));canvas.restoreState()
 # Explicitly join a heading with the complete next source block. Ordinary
 # keepWithNext alone does not reliably bridge an enclosing KeepTogether.
 joined=[];pending=[]
 for flow in story:
  if isinstance(flow,Paragraph) and flow.style.name in ['Title','Heading2','Heading3']:
   pending.append(flow)
  elif pending:
   content=flow._content if isinstance(flow,KeepTogether) else [flow]
   joined.append(KeepTogether(pending+content));pending=[]
  else:joined.append(flow)
 if pending:raise ValueError('Trailing heading without content')
 SimpleDocTemplate(str(destination),pagesize=letter,title=title,author='A1K Agentic SuperResearch',leftMargin=51,rightMargin=51,topMargin=48,bottomMargin=45).build(joined,onFirstPage=footer,onLaterPages=footer)

def renderer(html_bytes,manuscript,title,destination):
 payload=blocks(manuscript)
 with tempfile.TemporaryDirectory(prefix='frontier-render-') as temp:
  p=Path(temp)/'blocks.json';p.write_text(json.dumps(payload))
  proc=subprocess.run([RUNTIME,str(Path(__file__).resolve()),str(p),title,str(destination)],capture_output=True,timeout=120)
  if proc.returncode:raise RuntimeError(proc.stderr.decode()[:2000])
 return {'available':True,'renderer':'local-reportlab-markdown-and-six-explicit-math-mappings','attempts':[{'renderer':'reportlab','python_executable':RUNTIME,'exit_code':proc.returncode,'diagnostic_sha256':hashlib.sha256(proc.stdout+proc.stderr).hexdigest()}],'formula_mappings':[{'source':b['source'],'pdf_markup':b['text']} for b in payload if b['type']=='math'],'limitations':['Six displayed formulas use explicit source-to-display mappings; mathematical code blocks retain exact readable source notation.','PDF semantic tagging and accessibility conformance are not established.']}
if __name__=='__main__':write_pdf(json.loads(Path(sys.argv[1]).read_text()),sys.argv[2],Path(sys.argv[3]))
