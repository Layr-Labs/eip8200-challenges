"""Exact write-boundary discriminator for reuse of incumbent rowMem.
Not an arithmetic-only or final-memory test: every MSTORE must agree.
"""
import json, random
from pathlib import Path
from evm import VM, MASK, word
from test_current import source, BASE, S, setup

def stores(vm, stops):
    result=[]
    for _ in range(10000):
        if vm.steps and vm.pc in stops:
            return result,vm
        op=vm.d[vm.pc][0]
        addr=vm.s[0] if op=='MSTORE' else None
        vm.step()
        if addr is not None:result.append((addr,bytes(vm.mem)))
    raise AssertionError('row instruction cap')

def check(code, rowpc):
    raw=source(BASE);rng=random.Random(821282);cases=0;savings=[]
    for k in range(64):
        mem,_,_,_,pa,pb,pd=setup(8,k,rng)
        # Arbitrary scratch and MINV are intentional: row trace must not
        # silently acquire normalized/reduced/inverse hypotheses.
        if k<4:
            for a in range(8192,8512,32):word(mem,a,[0,1,MASK,MASK-1][k])
        word(mem,9376,rng.randrange(MASK+1))
        frame=[pb+224,pa-32,pb-32,pd,1939]+list(range(1000 if k==0 else 7))
        old,inc=stores(VM(raw,frame,mem,1974),{1974,2455})
        new,cand=stores(VM(code,frame,mem,rowpc),{rowpc,2637})
        for i in range(max(len(old),len(new))):
            assert i<len(old) and i<len(new),('store count',k,len(old),len(new))
            assert old[i]==new[i],('intermediate MSTORE differs',k,i,old[i][0],new[i][0])
        assert inc.mem==cand.mem and inc.s==cand.s
        savings.append(inc.gas-cand.gas);cases+=1
    return {'arbitrary_rows':cases,'stores_per_row':len(old),'row_savings':sorted(set(savings)),
            'all_intermediate_memory_equal':True}

def main():
    code=bytes.fromhex((S/'bytecode.hex').read_text())
    # The relocated prologue, selector and row entry retain their lengths.
    print(json.dumps(check(code,5407),indent=2))
if __name__=='__main__':main()
