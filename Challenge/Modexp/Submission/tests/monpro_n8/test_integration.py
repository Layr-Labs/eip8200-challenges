"""Cheap source packaging gate; NOT a Lean elaboration receipt."""
from pathlib import Path
import json, re, subprocess
from evm import decode
from test_current import S, W, BASE

def main():
    code=bytes.fromhex((S/'bytecode.hex').read_text())
    ins=list(decode(code).items())
    fast=S/'Proofs/Fast'
    files=[fast/x for x in ['Monpro.lean','MonproCore.lean','MonproN8Rows.lean',
        'MonproN8Memory.lean','MonproN8Mac.lean','MonproN8Paths.lean','Paths/P7.lean']]
    count=0
    for p in files:
        t=p.read_text()
        assert not re.search(r'\b(sorry|admit|axiom)\b',t),p
        for m in re.finditer(r'pushAt (\d+) (\d+) (\d+)',t):
            i,w,v=map(int,m.groups());pc,(op,arg,nxt)=ins[i]
            assert (op,arg or 0,nxt-pc-1)==('PUSH'+str(w),v,w),(p,m.group())
            count+=1
        for m in re.finditer(r'opAt (\d+) (?:\(\.(Dup|Swap) ⟨(\d+), by decide⟩\)|\.(\w+))',t):
            wanted=m[2].upper()+str(int(m[3])+1) if m[2] else m[4]
            assert ins[int(m[1])][1][0]==wanted,(p,m.group())
            count+=1
        for m in re.finditer(r'Artifact.instructionPC (\d+) = (\d+)',t):
            assert ins[int(m[1])][0]==int(m[2]),(p,m.group())
    seen=set(); visiting=set()
    def dfs(p):
        assert p not in visiting,('cycle',p)
        if p in seen:return
        visiting.add(p)
        for x in re.findall(r'^import (Challenge\.Modexp\.Submission[\w.]+)',p.read_text(),re.M):
            q=W/('/'.join(x.split('.'))+'.lean')
            assert q.exists(),q
            dfs(q)
        visiting.remove(p);seen.add(p)
    dfs(fast/'Exp.lean')
    assert fast/'MonproN8Rows.lean' in seen
    old=subprocess.check_output(['git','show',BASE+':Challenge/Modexp/Submission/Proofs/Fast/Monpro.lean'],cwd=W,text=True)
    new=(fast/'Monpro.lean').read_text()
    for name in ['gasSteps_monproFull','gasSteps_monproCsub','gasSteps_monproToCsub']:
        assert old.split('def '+name,1)[1].split(' :=',1)[0]==new.split('def '+name,1)[1].split(' :=',1)[0],name
    print(json.dumps({'located_claims':count,'import_modules':len(seen),
        'rows_reachable_from_Exp':True,'public_contracts_unchanged':True,
        'proof_holes':False,'compiled':False},indent=2))
if __name__=='__main__': main()
