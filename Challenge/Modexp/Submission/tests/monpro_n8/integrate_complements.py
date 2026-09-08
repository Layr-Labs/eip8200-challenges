"""Deterministic candidate-local relocation from a frozen PR776 source snapshot.
Never invokes a compiler, protected renderer write, scorer or upload.
Pending semantic audit is recorded separately; no eligibility inferred here.
"""
import re,json,hashlib,zipfile
from pathlib import Path
from repair_complements import build, ORIGINAL, S, HERE
from evm import decode
W=S.parents[2]
SNAP=W/'artifacts/pr776-before-complements.zip'

def snapshot():
    if not SNAP.exists():
        assert hashlib.sha256(bytes.fromhex((S/'bytecode.hex').read_text())).hexdigest()==ORIGINAL
        SNAP.parent.mkdir(exist_ok=True)
        with zipfile.ZipFile(SNAP,'w',zipfile.ZIP_DEFLATED) as z:
            for p in S.rglob('*.lean'):z.write(p,str(p.relative_to(S)))
            z.write(S/'bytecode.hex','bytecode.hex')
    with zipfile.ZipFile(SNAP) as z:return {n:z.read(n).decode() for n in z.namelist()}

def main():
    src=snapshot();old=bytes.fromhex(src['bytecode.hex']);new,pm,im,selected,controls=build(old)
    oi=list(decode(old).items());ni=list(decode(new).items());selected=set(selected)
    logs=[]
    def transform(name,text):
        stash=[]
        # Use unambiguous numbered token strings; numeric lexer excludes word chars.
        def hold(v):
            key='ZZRELOC_'+str(len(stash))+'_ZZ';stash.append((key,v));return key
        # Preserve comments and string literals rather than pretending documentation is proof.
        text=re.sub(r'/\-.*?\-/|--[^\n]*|"(?:\\.|[^"\\])*"',lambda m:hold(m[0]),text,flags=re.S)
        # Whole small interval-PC declarations carry both ordinal bounds and PCs.
        tablepat=r'(@\[simp\] (?:private )?theorem \w+ \((i|index) : Nat\).*?)(?=\n\n(?:def |theorem |@|end |ZZRELOC_|set_option)|\Z)'
        def table(m):
            t=m[0];var=m[2]
            if 'instructionPC '+var+' =' not in t:return t
            bounds=re.search(r'(\d+) ≤ '+var+r'\).*?'+var+r' ≤ (\d+)',t,re.S)
            arr=re.search(r'\[([\d,\s]+)\]',t)
            if not bounds or not arr:return t
            lo,hi=map(int,bounds.groups());nlo,nhi=im[lo],im[hi+1]-1
            vals=','.join(str(ni[j][0]) for j in range(nlo,nhi+1))
            t=t[:arr.start()]+hold('['+vals+']')+t[arr.end():]
            t=re.sub(r'(?<![\w])'+str(lo)+r'(?![\w])',hold(str(nlo)),t)
            t=re.sub(r'(?<![\w])'+str(hi)+r'(?![\w])',hold(str(nhi)),t)
            return t
        text=re.sub(tablepat,table,text,flags=re.S)
        text=re.sub(r'(pcFact\w* \w+) (\d+) (\d+)',lambda m:hold(m[1]+' '+str(im[int(m[2])])+' '+str(pm[int(m[3])])),text)
        text=re.sub(r'(window_table_update \w+ \w+ \w+ \d+ \d+) (\d+) (\d+) (\d+)',lambda m:hold(m[1]+' '+str(pm[int(m[2])])+' '+str(pm[int(m[3])])+' '+str(im[int(m[4])])),text)
        text=re.sub(r'(\binstructionPC )(\d+)( = )(\d+)',lambda m:hold(m[1]+str(im[int(m[2])])+m[3]+str(pm[int(m[4])])),text)
        def push(m):
            i,w,v=map(int,m.groups());p,(op,arg,nxt)=oi[i]
            assert (w,v)==(nxt-p-1,arg or 0),(name,m[0])
            if p in selected:return hold(f'pushAt {im[i]} 1 {((1<<256)-1)-v}, opAt {im[i]+1} .NOT')
            np,(nop,nv,nn)=ni[im[i]]
            return hold(f'pushAt {im[i]} {nn-np-1} {nv or 0}')
        text=re.sub(r'\bpushAt (\d+) (\d+) (\d+)',push,text)
        text=re.sub(r'\bopAt (\d+)',lambda m:hold('opAt '+str(im[int(m[1])])),text)
        text=re.sub(r'\b(instructionPC|isValidJumpDest_index) (\d+)',lambda m:hold(m[1]+' '+str(im[int(m[2])])),text)
        text=re.sub(r'(submissionInstructions\[)(\d+)(\]\?)',lambda m:hold(m[1]+str(im[int(m[2])])+m[3]),text)
        # Explicit program-counter slots disambiguate aligned PC vs memory constants.
        text=re.sub(r'(pc := (?:UInt256.ofNat )?)(\d+)',lambda m:hold(m[1]+str(pm[int(m[2])])),text)
        text=re.sub(r'(submissionBytecode )(\d+)( = true)',lambda m:hold(m[1]+str(pm[int(m[2])])+m[3]),text)
        # Remaining changed numerals are logged for complete semantic-context audit.
        # Aligned constants are data by default; explicit PC contexts above override.
        text=re.sub(r'(locatedSlice) (\d+) (\d+)',lambda m:hold(m[1]+' '+str(im[int(m[2])])+' '+str(im[int(m[2])+int(m[3])]-im[int(m[2])])),text)
        text=re.sub(r'(def \w*Index[^\n]*?: Nat := )(\d+)',lambda m:hold(m[1]+str(im[int(m[2])])),text)
        if name=='Proofs/Fast/Monpro.lean':text=re.sub(r'\b134\b',hold(str(pm[4205]-pm[4071])),text)
        def number(m):
            v=int(m[0])
            if v in pm and pm[v]!=v and v not in {3040,3072,3506,4096,4128,5120}:
                logs.append({'file':name,'old':v,'new':pm[v],'context':text[max(0,m.start()-65):m.end()+65]})
                return str(pm[v])
            return m[0]
        text=re.sub(r'(?<![\w])\d+(?![\w])',number,text)
        for key,value in reversed(stash):text=text.replace(key,value)
        return text
    # Defs has interval certificates and anchors. Rebuild those declarations from
    # decoded ordinals while retaining bounded prefix proofs and theorem names.
    defs=src['Proofs/Fast/Defs.lean']
    start=defs.index('private theorem fastPCAnchor0')
    end=defs.index('theorem jumpDest1196')
    block=defs[start:end];made=''
    anchors=re.findall(r'private theorem (fastPCAnchor\d+) :\s*Artifact.submissionArtifact.instructionPC (\d+) = (\d+) := by',block)
    for k,(name,i,p) in enumerate(anchors):
        i=im[int(i)];p=ni[i][0]
        made+=f'private theorem {name} :\n    Artifact.submissionArtifact.instructionPC {i} = {p} := by\n'
        if k==0:made+='  rfl\n\n'
        else:
            prevname,previ,_=anchors[k-1];previ=im[int(previ)];delta=i-previ
            made+=f'''  calc
    Artifact.submissionArtifact.instructionPC {i} =
        Artifact.submissionArtifact.instructionPC {previ} +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop {previ}).take {delta})).length :=
      instructionPC_add Artifact.submissionArtifact {previ} {delta}
    _ = {p} := by rw [{prevname}]; rfl

'''
    tables=re.findall(r'@\[simp\] theorem (\w+) \(i : Nat\)\s*\(hi : (\d+) ≤ i\) \(hii : i ≤ (\d+)\)',block)
    for name,lo,hi in tables:
        lo=im[int(lo)];hi=im[int(hi)+1]-1
        vals=','.join(str(ni[i][0]) for i in range(lo,hi+1))
        made+=f'''@[simp] theorem {name} (i : Nat) (hi : {lo} ≤ i) (hii : i ≤ {hi}) :
    Artifact.submissionArtifact.instructionPC i =
      ([{vals}] : List Nat)[i - {lo}]! := by
'''
        if name=='fullBasePC':made+='  interval_cases i <;> decide\n\n';continue
        anchor='fastPCAnchor'+name.removeprefix('fastPC')
        made+=f'''  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC ({lo} + (i - {lo})) := by rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC {lo} +
          (assembleBytes ((Artifact.submissionArtifact.instructions.drop {lo}).take (i - {lo}))).length :=
      instructionPC_add Artifact.submissionArtifact {lo} (i - {lo})
    _ = _ := by rw [{anchor}]; interval_cases i <;> rfl

'''
    for p in sorted(selected):
        oldidx=next(i for i,(pc,_) in enumerate(oi) if pc==p)
        idx=im[oldidx]+1
        made+=f'@[simp] theorem complementPC{oldidx} : Artifact.submissionArtifact.instructionPC {idx} = {ni[idx][0]} := by rfl\n'
    for value in [0,31]:
        made+=f'@[simp] theorem complementLiteral{value} : UInt256.lnot ({value} : UInt256) = ({((1<<256)-1)-value} : UInt256) := by decide\n'
    # Full-state semantic boundaries for every replacement, not only a literal
    # identity. The template preserves memory, environment, active words, and
    # all other fields; NOT needs one spare slot under runInstr's uniform cap.
    for p in sorted(selected):
        oldidx=next(i for i,(pc,_) in enumerate(oi) if pc==p)
        idx=im[oldidx];value=oi[oldidx][1][1];small=((1<<256)-1)-value
        pc=pm[p];endpc=pm[oi[oldidx][1][2]]
        made+=f'''\nset_option linter.unusedSimpArgs false in
 theorem runComplement{oldidx} (template : State) (rest : List UInt256)
    (hcap : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      [pushAt {idx} 1 {small}, opAt {idx+1} .NOT]
      {{ template with pc := UInt256.ofNat {pc}, stack := rest, halt := .Running }} =
    some {{ template with pc := UInt256.ofNat {endpc},
      stack := ({value} : UInt256) :: rest, halt := .Running }} := by
  have hpc0 : Artifact.submissionArtifact.instructionPC {idx} = {pc} := by rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC {idx+1} = {pc+2} := by rfl
  have hc : rest.length < 1024 := by omega
  simp [pushAt, opAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc0, hpc1, hc, hcap, complementLiteral{small},
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
'''
    src['Proofs/Fast/Defs.lean']=defs[:start]+'ZZDEFS_TABLES_ZZ\n'+defs[end:]
    active=set()
    def visit(name):
        if name in active:return
        active.add(name)
        for mod in re.findall(r'^import Challenge\.Modexp\.Submission\.(\S+)',src[name],re.M):
            visit(mod.replace('.','/')+'.lean')
    visit('Solution.lean')
    changed=[]
    for name,text in src.items():
        if not name.endswith('.lean') or name in ['Bytes.lean','Proofs/Bytecode/Artifact.lean']:continue
        if name not in active:
            if (S/name).read_text()!=text:(S/name).write_text(text)
            continue
        result=transform(name,text)
        if name=='Proofs/Fast/Defs.lean':result=result.replace('ZZDEFS_TABLES_ZZ',made)
        if name=='Bytecode.lean':result=re.sub(r'(submission(?:Bytecode|Bytes).size = )\d+',lambda m:m[1]+str(len(new)),result)
        if name=='Proofs/Bytecode/WindowHitByteSlices.lean':
            # Pin semantic template boundaries as well as the literal slices.
            boundary='\n/-- The reusable template starts at the exact relocated slice boundary. -/\n'
            boundary+='theorem byteStartPC_exact (byte : Fin 4) :\n'
            boundary+='    Artifact.submissionArtifact.instructionPC (byteStartIndex byte) = byteStartPC byte := by\n'
            boundary+='  fin_cases byte <;> rfl\n\n'
            boundary+='theorem segmentedBytePath_length (byte : Fin 4) :\n'
            boundary+='    (segmentedBytePath byte).length = (if byte.val = 3 then 47 else 48) := by\n'
            boundary+='  fin_cases byte <;> rfl\n\n'
            pos=result.rfind('end ')
            result=result[:pos]+boundary+result[pos:]
        if (S/name).read_text()!=result:(S/name).write_text(result)
        if result!=text:changed.append(name)
    # Independent exact binding emission; do NOT replay stale generate_traces.py.
    chunks=[new[i:i+64] for i in range(0,len(new),64)]
    t=src['Bytes.lean'].split('private abbrev submissionChunk0')[0]
    for i,c in enumerate(chunks):t+=f'private abbrev submissionChunk{i} : ByteArray := ByteArray.mk #[\n  '+', '.join(f'0x{x:02x}' for x in c)+'\n]\n\n'
    t+='abbrev submissionBytes : ByteArray :=\n  '+' ++\n  '.join(f'submissionChunk{i}' for i in range(len(chunks)))
    t+=f'\n\n@[simp] theorem submissionBytes_size : submissionBytes.size = {len(new)} := by\n  decide\n\nend Challenge.Modexp\n'
    (S/'Bytes.lean').write_text(t);(S/'bytecode.hex').write_text(new.hex()+'\n')
    pre,rest=src['Proofs/Bytecode/Artifact.lean'].split('def submissionInstructions : List Instr :=',1)
    _,post=rest.split('theorem submissionInstructions_count',1);items=[]
    for p,(op,v,nxt) in ni:
        if op.startswith('PUSH'):x=f'push {nxt-p-1} {v or 0}'
        elif op.startswith(('DUP','SWAP')):
            k=3 if op.startswith('DUP') else 4
            x='op (EvmSemantics.Operation.'+('Dup' if k==3 else 'Swap')+' { idx := '+str(int(op[k:])-1)+' })'
        else:x='op EvmSemantics.Operation.'+('INVALID' if op=='0xfe' else op)
        items.append('YulEvmCompiler.Instr.'+x)
    post=re.sub(r'submissionInstructions.length = \d+',f'submissionInstructions.length = {len(ni)}',post,count=1)
    (S/'Proofs/Bytecode/Artifact.lean').write_text(pre+'def submissionInstructions : List Instr :=\n['+',\n '.join(items)+']\n\ntheorem submissionInstructions_count'+post)
    (W/'artifacts/complement-relocation-contexts.json').write_text(json.dumps(logs,indent=2)+'\n')
    print(json.dumps({'modified_modules':len(changed),'context_occurrences_to_audit':len(logs),'bytes':len(new),'instructions':len(ni),'sha256':hashlib.sha256(new).hexdigest(),'eligible':False},indent=2))
if __name__=='__main__':main()
