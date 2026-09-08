"""Match incumbent rowC0 for arbitrary MINV, avoiding inverse premise in trace."""
from schedule import *
import random,json
from pathlib import Path

def c0(q,x,mu,out):
    q.arrange([x,mu])
    for op in ['DUP2','DUP2','MUL','SWAP1']:q.op(op)
    if 'K' in q.stack:q.dup('K')
    else:q.push(MASK)
    for op in ['SWAP1','DUP4','MULMOD','DUP2','DUP2','LT','SUB','DUP2','ISZERO','ISZERO','SUB','SUB']:q.op(op)
    q.stack[:2]=[out,mu]

if __name__=='__main__':
    rng=random.Random(1000);q=Schedule(['x','mu','frame']);c0(q,'x','mu','cm')
    for k in range(100):
        x,mu=[MASK,MASK] if k==0 else [rng.randrange(B) for _ in range(2)]
        v=VM(q.bytes(),[x,mu,999],bytes(9472)).run()
        assert v.s==[x*mu//B+int((x*mu)%B!=0),mu,999],v.s
    out={'cases':100,'bytes':len(q.bytes()),**v.stats()}
    Path(__file__).with_name('c0-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
