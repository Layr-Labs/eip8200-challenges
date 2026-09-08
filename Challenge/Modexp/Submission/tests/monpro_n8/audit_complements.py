"""Cheap exact closure audit, not a Lean compiler or universal proof receipt."""
import re,json,hashlib
from pathlib import Path
from repair_complements import S,HERE,build
from integrate_complements import snapshot,W
from evm import decode,INV

def main():
    code=bytes.fromhex((S/'bytecode.hex').read_text());ins=list(decode(code).items())
    src=snapshot();expected,pm,im,selected,ct=build(bytes.fromhex(src['bytecode.hex']))
    assert code==expected
    active=set();counts={'push':0,'op':0,'pc':0,'jump':0,'cached_pc':0,'pcFact':0};errors=[]
    def dfs(n):
        if n in active:return
        assert (S/n).exists(),n
        active.add(n)
        for m in re.findall(r'^import Challenge\.Modexp\.Submission\.(\S+)',(S/n).read_text(),re.M):dfs(m.replace('.','/')+'.lean')
    dfs('Solution.lean')
    for n in sorted(active):
        t=(S/n).read_text();t=re.sub(r'/\-.*?\-/|--[^\n]*','',t,flags=re.S)
        assert not re.search(r'\b(sorry|admit|axiom)\b',t),n
        for m in re.finditer(r'pushAt (\d+) (\d+) (\d+)',t):
            i,w,v=map(int,m.groups());pc,(op,arg,nxt)=ins[i]
            if (op,arg or 0,nxt-pc-1)!=('PUSH'+str(w),v,w):errors.append((n,m[0],'push mismatch'))
            counts['push']+=1
        for m in re.finditer(r'opAt (\d+) (?:\(\.(Dup|Swap) ⟨(\d+), by decide⟩\)|\.(\w+))',t):
            wanted=m[2].upper()+str(int(m[3])+1) if m[2] else m[4]
            if ins[int(m[1])][1][0]!=wanted:errors.append((n,m[0],'op mismatch'))
            counts['op']+=1
        for m in re.finditer(r'instructionPC (\d+) = (\d+)',t):
            if ins[int(m[1])][0]!=int(m[2]):errors.append((n,m[0],'pc mismatch'))
            counts['pc']+=1
        for m in re.finditer(r'isValidJumpDest Challenge.Modexp.submissionBytecode (\d+) = true :=\s*Artifact.isValidJumpDest_index (\d+)',t):
            p,i=map(int,m.groups())
            if ins[i][0]!=p or ins[i][1][0]!='JUMPDEST':errors.append((n,m[0],'jump mismatch'))
            counts['jump']+=1
        for m in re.finditer(r'pcFact\w* \w+ (\d+) (\d+)',t):
            if ins[int(m[1])][0]!=int(m[2]):errors.append((n,m[0],'pcFact mismatch'))
            counts['pcFact']+=1
        for m in re.finditer(r'instructionPC (i|index) =\s*\(?\[([\d,\s]+)\](?: : List Nat\))?\[\1 - (\d+)\]!',t):
            vals=list(map(int,re.findall(r'\d+',m[2])));base=int(m[3])
            if vals!=[ins[j][0] for j in range(base,base+len(vals))]:errors.append((n,'cached PC base '+str(base),'array mismatch'))
            counts['cached_pc']+=len(vals)
    bt=(S/'Bytes.lean').read_text();chunks=re.findall(r'private abbrev submissionChunk\d+ : ByteArray := ByteArray.mk #\[(.*?)\]',bt,re.S)
    assert b''.join(bytes(int(v,16) for v in re.findall(r'0x([0-9a-f]{2})',c)) for c in chunks)==code
    assert f'submissionBytes.size = {len(code)}' in bt
    at=(S/'Proofs/Bytecode/Artifact.lean').read_text();part=at.split('def submissionInstructions : List Instr :=',1)[1].split('theorem submissionInstructions_count',1)[0];enc=bytearray();INV['INVALID']=254
    for l in part.splitlines():
        m=re.search(r'Instr.push (\d+) (\d+)',l)
        if m:w,v=map(int,m.groups());enc.append(95+w);enc.extend(v.to_bytes(w,'big'));continue
        m=re.search(r'Operation.(Dup|Swap) \{ idx := (\d+) \}',l)
        if m:enc.append((128 if m[1]=='Dup' else 144)+int(m[2]));continue
        m=re.search(r'Instr.op EvmSemantics.Operation.(\w+)',l)
        if m:enc.append(INV[m[1]])
    assert bytes(enc)==code
    assert f'submissionInstructions.length = {len(ins)}' in at
    result={'bytes':len(code),'sha256':hashlib.sha256(code).hexdigest(),'active_modules':len(active),'counts':counts,'errors':errors,'compiled':False,'eligible':False}
    (W/'artifacts/complement-closure-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));assert not errors
if __name__=='__main__':main()
