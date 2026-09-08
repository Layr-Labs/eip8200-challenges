"""Discriminate every generated MAC contract using actual canonical bytes."""
import random,json
from evm import VM, B, MASK, read, word
from build_ordered import build,S

def main():
    code,_,bounds=build();assert code==bytes.fromhex((S/'bytecode.hex').read_text())
    rng=random.Random(12821282);cases=0;peak=0
    for phase,count in [('l1',8),('l2',7)]:
        for j in range(count):
            for k in range(16):
                mem=bytearray(rng.randbytes(9472));c=rng.randrange(B);y=rng.randrange(B)
                # Include T aliases and unaligned source addresses; these
                # trace contracts have only address fit, not nonaliasing.
                pa=[32,1024,8192,8224,8256,8480,9216,1031][k%8]
                if k==0:c=y=MASK
                rest=list(range(1013 if k==0 else 9))
                if phase=='l1':
                    xaddr=pa+32*(7-j);taddr=8480-32*j;dst=taddr
                    stack=[c,y,pa-32,MASK]+rest
                else:
                    xaddr=192-32*j;taddr=8448-32*j;dst=8480-32*j
                    stack=[c,y,MASK]+rest
                total=read(mem,xaddr)*y+read(mem,taddr)+c
                expected=bytearray(mem);word(expected,dst,total&MASK)
                vm=VM(code,stack,mem,bounds[f'{phase}_{j}']['pc']).run(stops=(bounds[f'{phase}_{j+1}']['pc'],),max_steps=100)
                expected_stack=[total//B]+stack[1:]
                assert vm.mem==expected and vm.s==expected_stack,(phase,j,k)
                assert vm.active==296 and vm.writes==[dst]
                peak=max(peak,vm.peak);cases+=1
    out={'actual_byte_MAC_cases':cases,'peak_stack':peak,'all_15_contracts':True,
         'aliases_and_unaligned_sources':True,'compiled':False}
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
