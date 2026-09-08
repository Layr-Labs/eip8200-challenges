"""Executed complement seams and decoded semantic boundary checks; no compiler."""
import hashlib,json,re
from evm import VM,decode,MASK
from integrate_complements import snapshot,W
from repair_complements import S,build

def main():
    src=snapshot(); old=bytes.fromhex(src['bytecode.hex'])
    new,pm,im,selected,_=build(old)
    assert new==bytes.fromhex((S/'bytecode.hex').read_text())
    oi=list(decode(old).items());ni=list(decode(new).items());sites=[]
    for p in selected:
        for depth in (0,7,1008,1022):
            stack=[(MASK-i*37)&MASK for i in range(depth)]
            mem=bytes(range(256))*40
            a=VM(old,stack,mem,p);a.step()
            b=VM(new,stack,mem,pm[p]);b.step();b.step()
            assert (a.s,a.mem,a.active,a.writes,a.reads)==(b.s,b.mem,b.active,b.writes,b.reads)
            assert b.pc==pm[a.pc] and b.gas==a.gas+3
            mutant=bytearray(new);mutant[pm[p]+1]^=1
            bad=VM(mutant,stack,mem,pm[p]);bad.step();bad.step()
            assert bad.s!=b.s
        sites.append({'old_pc':p,'new_pc':pm[p],'depths':[0,7,1008,1022],'negative_control':True})
    # Check all literal slice and parametric byte template boundaries against
    # the frozen source, not a hand-copied post-relocation expected constant.
    name='Proofs/Bytecode/WindowHitByteSlices.lean';oldtext=src[name];text=(S/name).read_text()
    oldbase=int(re.search(r'def byteStartIndex.*?: Nat := (\d+)',oldtext)[1])
    base=int(re.search(r'def byteStartIndex.*?: Nat := (\d+)',text)[1])
    boundaries=[]
    for byte in range(4):
        offsets=[0,5 if byte==3 else 6,24 if byte==3 else 25,47 if byte==3 else 48]
        for off in offsets:
            assert base+48*byte+off==im[oldbase+48*byte+off],('template ordinal',byte,off,base,im[oldbase])
            boundaries.append({'byte':byte,'offset':off,'index':base+48*byte+off,'pc':ni[base+48*byte+off][0]})
        count=47 if byte==3 else 48
        for k in range(count):
            assert oi[oldbase+48*byte+k][1][:2]==ni[base+48*byte+k][1][:2]
    pcs=list(map(int,re.search(r'def byteStartPC.*?\[([\d, ]+)\]',text,re.S)[1].split(',')))
    assert pcs==[ni[base+48*b][0] for b in range(4)],('template PCs',pcs)
    # Every explicit located path expands precisely at selected instructions,
    # including duplicated semantic branch paths and fallthrough tails.
    paths=0;occurrences=0
    # Capture declaration bodies; ordinals suffice for path sequence checks.
    def paths_in(t):
        out={}
        for m in re.finditer(r'^def (\w+)\b(.*?)(?=\n(?:def |theorem |set_option |end |/\-)|\Z)',t,re.M|re.S):
            ids=list(map(int,re.findall(r'(?:pushAt|opAt) (\d+)',m[2])))
            if ids:out[m[1]]=ids
        return out
    for name,t in src.items():
        if not name.endswith('.lean'):continue
        current=paths_in((S/name).read_text())
        for key,ids in paths_in(t).items():
            if not any(oi[i][0] in selected for i in ids):continue
            expected=[]
            for i in ids:
                expected.append(im[i])
                if oi[i][0] in selected:expected.append(im[i]+1);occurrences+=1
            assert current[key]==expected,(name,key)
            paths+=1
    definitions=(S/'Proofs/Fast/Defs.lean').read_text()
    assert len(re.findall(r'theorem runComplement\d+ ',definitions))==25
    for p in selected:
        i=next(i for i,(pc,_) in enumerate(oi) if pc==p)
        block=re.search(r'theorem runComplement'+str(i)+r'\b(.*?)(?=\nset_option|\ntheorem|\Z)',definitions,re.S)[1]
        assert f'pushAt {im[i]} 1 {MASK-oi[i][1][1]}, opAt {im[i]+1} .NOT' in block
        assert f'pc := UInt256.ofNat {pm[p]}' in block
        assert f'some {{ template with pc := UInt256.ofNat {pm[oi[i][1][2]]}' in block
        assert f'stack := ({oi[i][1][1]} : UInt256) :: rest' in block
    assert 'theorem byteStartPC_exact' in text and 'theorem segmentedBytePath_length' in text
    result={'sha256':hashlib.sha256(new).hexdigest(),'sites':sites,'site_count':len(sites),'executed_cases':len(sites)*4,'changed_paths':paths,'path_complement_occurrences':occurrences,'template_boundaries':boundaries,'full_state_proof_sources':25,'compiled':False}
    assert len(sites)==25
    (W/'artifacts/complement-semantic-tests.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('sites','template_boundaries')},indent=2))
if __name__=='__main__':main()
