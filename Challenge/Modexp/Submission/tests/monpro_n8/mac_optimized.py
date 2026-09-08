from schedule import *
import random,json
from pathlib import Path
D=Path(__file__).parent

def mac_keep_y(self,x,y,t,c,lo,hi):
    self.arrange([x,t,c,y])
    if 'K' in self.stack:self.dup('K')
    else:self.push(MASK)
    for op in ['DUP5','DUP3','MUL','SWAP2','DUP6','MULMOD','DUP2','DUP2','LT','SUB',
               'DUP4','DUP3','ADD','DUP1','SWAP5','GT','SUB','SUB',
               'SWAP1','DUP3','ADD','DUP1','SWAP3','GT','ADD','SWAP1']:
        self.op(op)
    self.stack[:3]=[lo,hi,y]

def main():
    rng=random.Random(821282);q=Schedule(['x','t','c','y','frame']);mac_keep_y(q,'x','y','t','c','lo','hi')
    for i in range(200):
        x,y,t,c=([MASK]*4 if not i else [rng.randrange(B) for _ in range(4)])
        v=VM(q.bytes(),[x,t,c,y,123],bytes(9472)).run()
        assert v.s==[(x*y+t+c)%B,(x*y+t+c)//B,y,123],v.s
    out={'cases':200,'bytes':len(q.bytes()),**v.stats()}
    (D/'mac-optimized-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
