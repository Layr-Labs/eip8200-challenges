"""PR776 candidate-side byte representation probe; does NOT update Lean proofs.
Never submit the output as an integrated candidate: relocation proof bindings remain.
No compiler/scorer. Preserve the primary and the integrated PR776 artifact.
"""
from pathlib import Path
import hashlib, json, random
from test_current import S, setup
from evm import decode, VM


def compact(old):
    ins=list(decode(old).items())
    dests={pc for pc,(op,arg,nxt) in ins if op=='JUMPDEST'}
    # Preserve widths of all address-valued PUSHes, avoiding fixed-point layout.
    # Reduce redundant numeric encodings only; PUSH0 replaces zero only in the
    # definitely unreachable padding after unconditional jump at pc1999.
    widths={}
    for pc,(op,arg,nxt) in ins:
        if op.startswith('PUSH'):
            width=nxt-pc-1
            minimum=max(1,((arg or 0).bit_length()+7)//8)
            if 2000<=pc<2130: minimum=0
            widths[pc]=width if arg in dests or width==0 else min(width,minimum)
    pcmap={}; outpc=0
    for pc,(op,arg,nxt) in ins:
        pcmap[pc]=outpc
        outpc+=1+widths[pc] if pc in widths else 1
    pcmap[len(old)]=outpc
    out=bytearray()
    for pc,(op,arg,nxt) in ins:
        if pc in widths:
            width=widths[pc]
            value=pcmap[arg] if arg in dests else (arg or 0)
            assert value < 256**width if width else value==0
            out.append(95+width);out.extend(value.to_bytes(width,'big'))
        else:out.append(old[pc])
    return bytes(out),pcmap


def main():
    old=bytes.fromhex((S/'bytecode.hex').read_text())
    assert hashlib.sha256(old).hexdigest()=='ce0325cee4eef2ab9efa8c3b28a88cd74d0a44f698697209bc45d4179f04c4fc'
    new,pcmap=compact(old)
    rng=random.Random(776);cases=0;gas={}
    for n in [2,3,4,5,7,8,9,16,32]:
        for k in range(32 if n==8 else 4):
            mem,a,b,m,pa,pb,pd=setup(n,k,rng)
            # The subroutine returns to the entry JUMPDEST in this harness.
            frame=[pa,pb,pd,1939]+list(range(7))
            lhs=VM(old,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            rhs=VM(new,[pa,pb,pd,pcmap[1939]]+frame[4:],mem,pcmap[1939]).run(stops=(pcmap[1939],),max_steps=250000)
            assert lhs.mem==rhs.mem and lhs.s==rhs.s,(n,k)
            assert lhs.gas==rhs.gas,(n,k,lhs.gas,rhs.gas)
            cases+=1;gas[str(n)]=lhs.gas-rhs.gas
    here=Path(__file__).parent
    (here/'pr776-compact-probe.hex').write_text(new.hex()+'\n')
    receipt={'original_bytes':len(old),'original_sha256':hashlib.sha256(old).hexdigest(),'bytes':len(new),'sha256':hashlib.sha256(new).hexdigest(),'canonical_chunks':(len(new)+63)//64,'opcode_cases':cases,'gas_change_vs_PR776':gas,'eligible':False,'blocker':'Prototype only: global PC/width relocation has not been integrated into active Lean proofs; generated Artifact recursion not compiler-checked. Do not upload.','pcmap':pcmap}
    (here/'pr776-compact-probe.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='pcmap'},indent=2))
if __name__=='__main__': main()
