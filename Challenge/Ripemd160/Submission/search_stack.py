"""Search local stack-only rewrites using the published raw template inputs.
Results are hypotheses, not correctness proofs; execute bytecode then check Lean.
"""
import re
from pathlib import Path
from collections import deque
R=Path(__file__).parent/'Proofs/Bytecode'

def stk_op(s,op):
 s=list(s)
 if op[0]=='D':
  if op[1]>=len(s):return None
  s.insert(0,s[op[1]])
 elif op[0]=='S':
  if op[1]+1>=len(s):return None
  s[0],s[op[1]+1]=s[op[1]+1],s[0]
 else:s=s[1:]
 return tuple(s)

def solve(start,end,depth):
 if start==end:return []
 need=set(end);ops=[('D',i) for i in range(min(16,len(end)))] + [('S',i) for i in range(min(16,len(end)-1))]+[('P',0)]
 q=deque([(start,())]);seen={start}
 while q:
  s,path=q.popleft()
  if len(path)>=depth:continue
  for o in ops:
   t=stk_op(s,o)
   if t is None or len(t)>len(end)+1 or len(t)<len(end)-1 or t in seen or not need.issubset(set(t)):continue
   p=path+(o,)
   if t==end:return p
   seen.add(t);q.append((t,p))
 return None

def binary(name,a,b):
 if name in ['ADD','MUL','AND','OR','XOR']:
  if name in ['AND','OR'] and a==b:return a
  if name=='XOR' and a==b:return '0'
  a,b=sorted([a,b])
 return name+'('+a+','+b+')'

for f in sorted(R.glob('Stagger*Raw.lean')):
 text=f.read_text()
 m=re.search(r'def inputStack .*? :=\s*\[(.*?)\] \+\+ rho',text,re.S)
 if not m:continue
 start=[]
 for val in re.split(r',\s*(?!by decide)',m[1]):
  val=val.strip()
  if not val:continue
  val=re.sub(r'\(UInt256.ofNat (\d+)\)',r'\1',val)
  start.append(val)
 start+=['rho'+str(i) for i in range(10)]
 m=re.search(r'def template : List Instr :=\s*\[(.*?)\]\s*def inputStack',text,re.S)
 if not m:continue
 rows=re.findall(r'\.op \(\.(Dup|Swap) ⟨(\d+), by decide⟩\)|\.op \.(\w+)|\.push ⟨(\d+), by decide⟩ \(UInt256.ofNat (\d+)\)',m[1])
 s=tuple(start);i=0
 while i<len(rows):
  a,n,op,w,v=rows[i]
  if a:
   j=i;run=[];t=s
   while j<len(rows) and (rows[j][0] or rows[j][2]=='POP'):
    x,k,name,_,_=rows[j];o=(x[0],int(k)) if x else ('P',0);run.append(o);t=stk_op(t,o);j+=1
   if len(run)>=2 and len(run)<=5:
    # retain the unchanged long suffix; prune search to useful prefix only
    length=min(18,max([k+2 for _,k in run])+len(run)+2)
    suffix=s[length:]
    if t[-len(suffix):]==suffix if suffix else True:
     ee=t[:-len(suffix)] if suffix else t
     pp=solve(s[:length],ee,len(run)-1)
     if pp is not None:print(f.name,'index',i,'old',run,'new',pp,flush=True)
   s=t;i=j;continue
  if w:s=(v,)+s
  elif op in ['ADD','MUL','SUB','AND','OR','XOR','DIV','SHR','SHL','SAR','LT','GT','EQ']:
   s=(binary(op,s[0],s[1]),)+s[2:]
  elif op=='MULMOD':s=('MODMUL('+','.join(s[:3])+')',)+s[3:]
  elif op=='NOT':s=('NOT('+s[0]+')',)+s[1:]
  elif op=='MLOAD':s=('LOAD('+s[0]+')',)+s[1:]
  elif op=='MSTORE':s=s[2:]
  elif op=='POP':s=s[1:]
  elif op=='JUMPDEST':pass
  else:break
  i+=1
