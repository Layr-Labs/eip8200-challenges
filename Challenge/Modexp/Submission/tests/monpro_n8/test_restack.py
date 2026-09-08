"""Fresh-pin active closure and preservation audit; no proof elaboration."""
from pathlib import Path
import re,json,subprocess
from test_current import S,W,BASE,source
from evm import decode

def main():
    code=bytes.fromhex((S/'bytecode.hex').read_text()); ins=list(decode(code).items())
    base=source(BASE)
    bt=(S/'Bytes.lean').read_text()
    chunks=re.findall(r'private abbrev submissionChunk(\d+) : ByteArray := ByteArray.mk #\[(.*?)\]',bt,re.S)
    assert [int(i) for i,_ in chunks]==list(range(len(chunks)))
    literals=[bytes(int(x,16) for x in re.findall(r'0x([0-9a-f]{2})',body)) for _,body in chunks]
    assert all(len(c)==64 for c in literals[:-1]) and len(literals[-1])==len(code)%64
    assert b''.join(literals)==code
    for m in re.finditer(r'submissionChunk(\d+)\.size\s*=\s*(\d+)',bt):
        assert len(literals[int(m[1])])==int(m[2])
    assert f'submissionBytes.size = {len(code)}' in bt
    assert f'submissionInstructions.length = {len(ins)}' in (S/'Proofs/Bytecode/Artifact.lean').read_text()
    assert code[:1939]==base[:1939] and code[1944:len(base)]==base[1944:]
    seen=set(); visiting=set()
    def walk(p):
        assert p not in visiting,('cycle',p)
        if p in seen:return
        visiting.add(p)
        for mod in re.findall(r'^import (Challenge\.Modexp\.Submission[\w.]*)',p.read_text(),re.M):
            q=W/('/'.join(mod.split('.'))+'.lean'); assert q.exists(),q;walk(q)
        visiting.remove(p);seen.add(p)
    walk(S/'Solution.lean')
    assert S/'Proofs/Fast/MonproN8Rows.lean' in seen
    counts={'push':0,'op':0,'pc':0,'jump':0};errors=[]
    for p in sorted(seen):
        t=p.read_text()
        assert not re.search(r'\b(sorry|admit|axiom)\b',t),p
        assert not re.search(r'^(<<<<<<<|=======|>>>>>>>)',t,re.M),p
        for m in re.finditer(r'pushAt\s+(\d+)\s+(\d+)\s+(\d+)',t):
            i,w,v=map(int,m.groups());pc,(op,arg,nxt)=ins[i]
            if (op,arg or 0,nxt-pc-1)!=('PUSH'+str(w),v,w):errors.append((str(p.relative_to(S)),m.group(),ins[i]))
            counts['push']+=1
        for m in re.finditer(r'opAt\s+(\d+)\s+(?:\(\.(Dup|Swap)\s+⟨(\d+),\s*by decide⟩\)|\.(\w+))',t):
            wanted=m[2].upper()+str(int(m[3])+1) if m[2] else m[4]
            if ins[int(m[1])][1][0]!=wanted:errors.append((str(p.relative_to(S)),m.group(),ins[int(m[1])]))
            counts['op']+=1
        for m in re.finditer(r'Artifact\.instructionPC\s+(\d+)\s*=\s*(\d+)',t):
            if ins[int(m[1])][0]!=int(m[2]):errors.append((str(p.relative_to(S)),m.group(),ins[int(m[1])]))
            counts['pc']+=1
        for m in re.finditer(r'Decode\.isValidJumpDest\s+Challenge\.Modexp\.submissionBytecode\s+(\d+)\s*=\s*true\s*:=\s*Artifact\.isValidJumpDest_index\s+(\d+)',t):
            if ins[int(m[2])][0]!=int(m[1]) or ins[int(m[2])][1][0]!='JUMPDEST':errors.append((str(p.relative_to(S)),m.group()))
            counts['jump']+=1
    print(json.dumps({'active_modules':len(seen),'claims':counts,'errors':errors,'public_window_bytes_preserved':True,'compiled':False},indent=2))
    assert not errors
if __name__=='__main__':main()
