"""Local ReportLab renderer preserving the accepted source and paragraph continuity.

This is a rendering adapter, not a scholarly or publication gate. LaTeX remains
readable source notation and the PDF does not claim semantic tagging.
"""
from pathlib import Path
import html,sys,json,subprocess,tempfile,hashlib
RUNTIME='/home/user/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3'
def write_pdf(manuscript,title,destination):
 from reportlab.lib.styles import getSampleStyleSheet
 from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,KeepTogether
 from reportlab.lib.pagesizes import letter
 from reportlab.pdfbase import pdfmetrics
 from reportlab.pdfbase.ttfonts import TTFont
 styles=getSampleStyleSheet();story=[]
 pdfmetrics.registerFont(TTFont('ReviewSerif','/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf'))
 pdfmetrics.registerFont(TTFont('ReviewSans','/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'))
 for style in styles.byName.values(): style.fontName='ReviewSerif'
 styles['BodyText'].fontSize=9;styles['BodyText'].leading=12.5
 styles['Title'].fontName='ReviewSans';styles['Title'].fontSize=22;styles['Title'].leading=27
 styles['Heading2'].fontName='ReviewSans';styles['Heading2'].fontSize=13;styles['Heading2'].leading=17
 styles['Heading3'].fontName='ReviewSans';styles['Heading3'].fontSize=11;styles['Heading3'].leading=14
 for block in manuscript.decode().split('\n\n'):
  if not block.strip(): continue
  if block.startswith('# '): text,title_style=title,styles['Title']
  elif block.startswith('## '): text,title_style=block[3:].strip(),styles['Heading2']
  elif block.startswith('### '): text,title_style=block[4:].strip(),styles['Heading3']
  else: text,title_style=block,styles['BodyText']
  story.append(KeepTogether([Paragraph(html.escape(text).replace('\n','<br/>'),title_style),Spacer(1,7)]))
 note='A1K Agentic SuperResearch · Local automated publication. Review records and artifact hashes describe checks performed locally; they do not establish external authentication, statistical reviewer independence, or independent human certification.'
 story.append(KeepTogether([Spacer(1,10),Paragraph(html.escape(note),styles['BodyText'])]))
 def footer(canvas,doc):
  canvas.saveState();canvas.setFont('Helvetica',7);canvas.setFillColorRGB(.3,.35,.42);canvas.drawCentredString(letter[0]/2,25,'A1K Agentic SuperResearch | '+str(doc.page));canvas.restoreState()
 SimpleDocTemplate(str(destination),pagesize=letter,title=title,author='A1K Agentic SuperResearch',leftMargin=51,rightMargin=51,topMargin=48,bottomMargin=45).build(story,onFirstPage=footer,onLaterPages=footer)
def renderer(html_bytes,manuscript,title,destination):
 with tempfile.TemporaryDirectory(prefix='frontier-render-') as temp:
  p=Path(temp)/'manuscript.md';p.write_bytes(manuscript)
  proc=subprocess.run([RUNTIME,str(Path(__file__).resolve()),str(p),title,str(destination)],capture_output=True,timeout=120)
  if proc.returncode: raise RuntimeError(proc.stderr.decode()[:1000])
 return {'available':True,'renderer':'local-reportlab-paragraph-continuity','attempts':[{'renderer':'reportlab','python_executable':RUNTIME,'exit_code':proc.returncode,'diagnostic_sha256':hashlib.sha256(proc.stdout+proc.stderr).hexdigest()}],'limitations':['LaTeX and Markdown inline notation remain readable source text in PDF; consult Markdown for exact notation.','PDF semantic tagging and accessibility conformance are not established.']}
if __name__=='__main__': write_pdf(Path(sys.argv[1]).read_bytes(),sys.argv[2],Path(sys.argv[3]))
