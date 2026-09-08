"""Bounded actual-opcode regression. Not scorer or universal proof.
Run from any cwd: python3 <this file>. Requires git objects for both controls.
"""
from pathlib import Path
import subprocess, random, json, re, hashlib
from evm import VM, B, MASK, word, block, decode
S=Path(__file__).resolve().parents[2]
W=S.parents[2]
BASE='ae7bee26443011c5ce256e58bd913185fb933403'
PUBLIC='02d875253867295325faabfd989b4b4819b61989'
def source(sha):
    return bytes.fromhex(subprocess.check_output(['git','show',sha+':Challenge/Modexp/Submission/bytecode.hex'],cwd=W,text=True))

def setup(n,k,rng):
    R=B**n
    m=([R-1,R//2+1,B**(n-1)+1][k] if k<3 else rng.randrange(1,R)|1)
    a=[m-1,0,1][k] if k<3 else rng.randrange(m)
    b=[R-1,0,R-1][k] if k<3 else rng.randrange(R)
    pa,pb,pd=[(1024,2048,1024),(1024,1024,1024),(1024,2048,2048),(1024,2048,3072)][k%4]
    if pa==pb:b=a
    mem=bytearray(rng.randbytes(9472))
    block(mem,0,m,n);block(mem,pa,a,n);block(mem,pb,b,n)
    for addr,val in [(9344,32*n),(9376,-pow(m,-1,B)),(9408,32*n-32),(9440,8224+32*n)]:word(mem,addr,val)
    return mem,a,b,m,pa,pb,pd

def main():
    raw=source(BASE); public=source(PUBLIC); code=bytes.fromhex((S/'bytecode.hex').read_text())
    assert len(code)==6097
    assert code[:1939]==raw[:1939] and code[1944:len(raw)]==raw[1944:]
    assert code[1939:1944]==bytes.fromhex('5b6114e756')
    # Independently reconstruct both complete binding surfaces.
    t=(S/'Bytes.lean').read_text()
    chunks=re.findall(r'private abbrev submissionChunk\d+ : ByteArray := ByteArray.mk #\[(.*?)\]',t,re.S)
    assert bytes(int(x,16) for c in chunks for x in re.findall(r'0x([0-9a-f]{2})',c))==code
    assert f'submissionBytes.size = {len(code)}' in t
    a=(S/'Proofs/Bytecode/Artifact.lean').read_text().split('def submissionInstructions : List Instr :=',1)[1].split('theorem submissionInstructions_count',1)[0]
    ins=[]
    for l in a.splitlines():
        if 'Instr.push' in l:
            w,v=map(int,re.search(r'Instr.push (\d+) (\d+)',l).groups());ins.append(bytes([95+w])+v.to_bytes(w,'big'))
        elif 'Instr.op' in l:
            from evm import INV
            INV['INVALID']=254
            mm=re.search(r'Operation.(Dup|Swap) \{ idx := (\d+) \}',l)
            if mm:ins.append(bytes([(128 if mm[1]=='Dup' else 144)+int(mm[2])]))
            else:ins.append(bytes([INV[re.search(r'Operation.(\w+)',l)[1]]]))
    assert b''.join(ins)==code
    assert f'submissionInstructions.length = {len(ins)}' in (S/'Proofs/Bytecode/Artifact.lean').read_text()
    # Audit every newly generated located opcode, literal PC and jump fact.
    paths=(S/'Proofs/Fast/MonproN8Paths.lean').read_text(); decoded=list(decode(code).items()); path_count=0
    for l in paths.splitlines():
        mm=re.search(r'pushAt (\d+) (\d+) (\d+)',l)
        if mm:
            i,w,v=map(int,mm.groups());p,(op,arg,nxt)=decoded[i]
            assert (op,arg or 0,nxt-p-1)==('PUSH'+str(w),v,w)
            path_count+=1
        mm=re.search(r'opAt (\d+) (.*?)(?:,?$)',l)
        if mm:
            i=int(mm[1]); op=decoded[i][1][0]; text=mm[2]
            if op.startswith(('DUP','SWAP')):
                k=3 if op.startswith('DUP') else 4
                assert ('Dup' if k==3 else 'Swap') in text and '⟨'+str(int(op[k:])-1)+',' in text
            else: assert '.'+op in text
            path_count+=1
        mm=re.search(r'Artifact.instructionPC (\d+) = (\d+)',l)
        if mm: assert decoded[int(mm[1])][0]==int(mm[2])
    assert path_count==len(decoded)-len(decode(raw))+3
    rng=random.Random(621282);rows={};count=0;peak=0
    for n in [2,3,4,5,7,8,9,16,32]:
        savings=[];pubs=[]
        for k in range(32 if n in [4,8] else 2):
            mem,aa,b,m,pa,pb,pd=setup(n,k,rng)
            frame=[pa,pb,pd,1939]+list(range(1008 if k==0 else 7))
            inc=VM(raw,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            cand=VM(code,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            assert cand.mem==inc.mem and cand.s==inc.s==frame[4:],(n,k)
            assert int.from_bytes(cand.mem[pd:pd+32*n],'big')==(aa*b*pow(B**n,-1,m))%m
            assert cand.active==inc.active==296
            savings.append(inc.gas-cand.gas);peak=max(peak,cand.peak);count+=1
            # PR750 CIOS2 entry is pc4057 (not its legacy MONPRO entry).
            if n in [4,8]:
                p=VM(public,frame,mem,4057).run(stops=(1939,),max_steps=250000)
                assert p.s==cand.s and p.mem==cand.mem
                pubs.append(p.gas-cand.gas)
        rows[n]={'cases':len(savings),'saved_vs_current':sorted(set(savings)),'saved_vs_PR750':sorted(set(pubs))}
    assert rows[8]['saved_vs_current']==[3852], rows
    assert all(v['saved_vs_current']==[-54] for n,v in rows.items() if n!=8)
    # Negative control: wrong carry comparison of identical arity must fail.
    mutant=bytearray(code)
    pc=next(pc for pc,(op,_,_) in decode(code).items() if pc>5407 and op=='GT')
    mutant[pc]=0x14
    detected=False
    for k in range(16):
        mem,_,_,_,pa,pb,pd=setup(8,k,rng);frame=[pa,pb,pd,1939,123]
        good=VM(code,frame,mem,1939).run(stops=(1939,))
        bad=VM(mutant,frame,mem,1939).run(stops=(1939,))
        if good.mem!=bad.mem:
            detected=True
            break
    assert detected, 'carry mutation survived bounded negative control'
    result={'cases':count,'peak_stack':peak,'by_width':rows,'mutation_detected':pc,'binding_reconstruction':True,'sha256':hashlib.sha256(code).hexdigest(),'eligible':False,'proof_status':'row/full contract source integrated; Lean elaboration not run'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
