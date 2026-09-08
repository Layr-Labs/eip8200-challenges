"""Same-candidate size repair. Build/test only until --emit is integrated.
Select the fewest PUSH32 complement expansions meeting incumbent byte envelope.
Retain every instruction, including JUMPI fallthroughs. No dead-code assumptions.
"""
from pathlib import Path
import hashlib,json,random
from evm import decode, VM, MASK
from test_current import S,setup,source
BASE='95c320bbaf39df43d7f14cd17b5106228ead9312'
HERE=Path(__file__).parent
ORIGINAL='ce0325cee4eef2ab9efa8c3b28a88cd74d0a44f698697209bc45d4179f04c4fc'

def build(old):
    ins=list(decode(old).items())
    eligible=[p for p,(op,v,_) in ins if op=='PUSH32' and v in (MASK,MASK-31)]
    need=(len(old)-5351+29)//30
    selected=set(eligible[-need:])
    pm={};im={};np=ni=0
    for i,(p,(op,v,nxt)) in enumerate(ins):
        pm[p]=np;im[i]=ni
        np+=3 if p in selected else nxt-p
        ni+=2 if p in selected else 1
    pm[len(old)]=np;im[len(ins)]=ni
    dests={p for p,(op,_,_) in ins if op=='JUMPDEST'}
    controls=[];new=bytearray()
    for i,(p,(op,v,nxt)) in enumerate(ins):
        if p in selected:new.extend([0x60,MASK-v,0x19])
        elif p==4062:
            # Four equal-size computed-jump copies: relocate their stride too.
            stride=pm[4205]-pm[4071]
            assert all(pm[4071+134*k]==pm[4071]+stride*k for k in range(4))
            new.extend([0x61,*stride.to_bytes(2,'big')])
        elif op.startswith('PUSH') and v in dests:
            # Every address candidate is retained in a reviewable manifest.
            controls.append({'pc':p,'value':v,'new_value':pm[v],'next':ins[i+1][1][0]})
            new.append(old[p]);new.extend(pm[v].to_bytes(nxt-p-1,'big'))
        else:new.extend(old[p:nxt])
    return bytes(new),pm,im,sorted(selected),controls

def main():
    import zipfile
    with zipfile.ZipFile(S.parents[2]/'artifacts/pr776-before-complements.zip') as frozen:
        old=bytes.fromhex(frozen.read('bytecode.hex').decode())
    assert hashlib.sha256(old).hexdigest()==ORIGINAL
    new,pm,im,selected,controls=build(old)
    assert len(new)<=5351 and len(new)+30>5351
    rng=random.Random(780);cases=0;gas={};raw=source(BASE)
    for n in [2,3,4,5,7,8,9,16,32]:
        gains=[];deltas=[]
        for k in range(32 if n==8 else 4):
            mem,a,b,m,pa,pb,pd=setup(n,k,rng)
            frame=[pa,pb,pd,1939]+list(range(1008 if k==0 else 7))
            lhs=VM(old,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            rhs=VM(new,[pa,pb,pd,pm[1939]]+frame[4:],mem,pm[1939]).run(stops=(pm[1939],),max_steps=250000)
            inc=VM(raw,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            assert lhs.mem==rhs.mem==inc.mem and lhs.s==rhs.s==inc.s,(n,k)
            assert lhs.active==rhs.active==inc.active
            deltas.append(rhs.gas-lhs.gas);gains.append(inc.gas-rhs.gas);cases+=1
        gas[n]={'extra_vs_pr776':sorted(set(deltas)),'saving_vs_incumbent':sorted(set(gains))}
    # The test must detect a wrong complement, not just exercise dispatch.
    mutant=bytearray(new);mutant[pm[4135]+1]^=1
    detected=False
    for k in range(8):
        mem,*_,pa,pb,pd=setup(32,k,rng);frame=[pa,pb,pd,1939,123]
        try:
            good=VM(new,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            bad=VM(mutant,frame,mem,1939).run(stops=(1939,),max_steps=250000)
            detected |= good.mem!=bad.mem or good.s!=bad.s
        except (AssertionError,RuntimeError):detected=True
    assert detected,'wrong complement mutation survived'
    receipt={'original_sha256':ORIGINAL,'bytes':len(new),'sha256':hashlib.sha256(new).hexdigest(),'chunks':(len(new)+63)//64,'selected':selected,'pcmap':pm,'indexmap':im,'controls':controls,'cases':cases,'gas':gas,'negative_control_detected':detected,'base':BASE,'compiled':False,'eligibility':'Component execution receipt only; see artifacts/complement-integration-receipt.json for source packaging status.'}
    (HERE/'repair-complements.hex').write_text(new.hex()+'\n')
    (HERE/'repair-complements.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['pcmap','indexmap','controls']},indent=2))
if __name__=='__main__':main()
