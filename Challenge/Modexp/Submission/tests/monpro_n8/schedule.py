"""Explicit opcode stack scheduler; no pseudo arithmetic instructions emitted."""
from evm import *

class Schedule:
    def __init__(self,stack):self.stack=list(stack);self.ops=[];self.peak=len(stack);self.access=0
    def op(self,name,arg=None):
        s=self.stack;self.ops.append((name,arg))
        if name=='PUSH':s.insert(0,('const',arg&MASK))
        elif name.startswith('DUP'):
            n=int(name[3:]);assert n<=16,('DUP overflow',n,s)
            self.access=max(self.access,n);s.insert(0,s[n-1])
        elif name.startswith('SWAP'):
            n=int(name[4:]);assert 1<=n<=16,('SWAP overflow',n,s)
            self.access=max(self.access,n+1);s[0],s[n]=s[n],s[0]
        elif name=='POP':s.pop(0)
        else:
            arity=3 if name in ('MULMOD','ADDMOD') else (2 if name in ('ADD','SUB','MUL','LT','GT','EQ','AND','OR','MSTORE') else 1)
            args=tuple(s[:arity]);del s[:arity]
            if name!='MSTORE':s.insert(0,(name,args))
        self.peak=max(self.peak,len(s))
    def label(self,name):self.stack[0]=name
    def push(self,v,label=None):self.op('PUSH',v);self.label(label if label else ('const',v&MASK))
    def dup(self,name,label=None):
        self.op('DUP'+str(self.stack.index(name)+1))
        if label:self.label(label)
    def take(self,name):
        k=self.stack.index(name)
        if k:self.op('SWAP'+str(k))
    def drop(self,name):self.take(name);self.op('POP')
    def arrange(self,front):
        # Place target prefix without disturbing any item below its maximum
        # depth. Three transpositions suffice to swap two non-top entries.
        for i,name in enumerate(front):
            k=self.stack.index(name)
            if k==i:continue
            if i==0:self.op('SWAP'+str(k))
            elif k==0:self.op('SWAP'+str(i))
            else:
                self.op('SWAP'+str(k));self.op('SWAP'+str(i));self.op('SWAP'+str(k))
        assert self.stack[:len(front)]==front
    def load(self,addr,label):self.push(addr);self.op('MLOAD');self.label(label)
    def store(self,name,addr):self.take(name);self.push(addr);self.op('MSTORE')
    def binary(self,op,a,b,out,keep=()):
        if a in keep:self.dup(a,'argA');a='argA'
        if b in keep:self.dup(b,'argB');b='argB'
        self.arrange([a,b]);self.op(op);self.label(out)
    def mac(self,x,y,t,c,lo,hi):
        self.arrange([x,y,t,c])
        for op in ['DUP2','DUP2','MUL','SWAP2'] :self.op(op)
        self.push(MASK)
        for op in ['SWAP2','MULMOD','DUP2','DUP2','LT','SWAP1','SUB','DUP2','SWAP1','SUB',
                   'SWAP1','DUP3','ADD','DUP3','DUP2','LT','SWAP1','SWAP2','ADD','SWAP2','POP',
                   'DUP3','ADD','DUP3','DUP2','LT','SWAP1','SWAP2','ADD','SWAP2','POP']:
            self.op(op)
        self.stack[:2]=[lo,hi]
    def bytes(self):return assemble(self.ops)

if __name__=='__main__':
    import random,json
    rng=random.Random(21282);q=Schedule(['x','y','t','c','frame']);q.mac('x','y','t','c','lo','hi')
    for i in range(100):
        x,y,t,c=[rng.randrange(B) for _ in range(4)] if i else [MASK]*4
        vm=VM(q.bytes(),[x,y,t,c,123],bytes(9472)).run()
        assert vm.s==[(x*y+t+c)%B,(x*y+t+c)//B,123],(vm.s,x,y,t,c)
    print(json.dumps(dict(cases=100,**vm.stats(),bytes=len(q.bytes()))))
