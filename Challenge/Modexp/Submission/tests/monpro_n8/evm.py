"""Small bounded Osaka instruction seam interpreter. Not an official scorer.
Top of stack is index zero. Memory byte-addressed; activeWords defaults to
296, the actual MONPRO contract. No evaluator/test corpus is read.
"""
from collections import Counter
from pathlib import Path
B=1<<256; MASK=B-1
SOURCE=Path(__file__).resolve().parents[2]/'bytecode.hex'
OPS={0:'STOP',1:'ADD',2:'MUL',3:'SUB',4:'DIV',6:'MOD',8:'ADDMOD',9:'MULMOD',10:'EXP',16:'LT',17:'GT',20:'EQ',21:'ISZERO',22:'AND',23:'OR',24:'XOR',25:'NOT',26:'BYTE',27:'SHL',28:'SHR',53:'CALLDATALOAD',54:'CALLDATASIZE',55:'CALLDATACOPY',80:'POP',81:'MLOAD',82:'MSTORE',83:'MSTORE8',86:'JUMP',87:'JUMPI',88:'PC',89:'MSIZE',90:'GAS',91:'JUMPDEST',94:'MCOPY',95:'PUSH0',243:'RETURN'}
INV={v:k for k,v in OPS.items()}
def decode(code):
    d={}; pc=0
    while pc<len(code):
        op=code[pc]; w=op-95 if 96<=op<=127 else 0
        name='PUSH'+str(w) if w else ('DUP'+str(op-127) if 128<=op<=143 else ('SWAP'+str(op-143) if 144<=op<=159 else OPS.get(op,hex(op))))
        d[pc]=(name,int.from_bytes(code[pc+1:pc+1+w],'big') if w else None,pc+1+w); pc+=1+w
    return d

def assemble(ops):
    code=bytearray()
    for name,arg in ops:
        if name=='PUSH':
            arg &=MASK
            if arg==0: code.append(95)
            else:
                w=(arg.bit_length()+7)//8; code.append(95+w); code.extend(arg.to_bytes(w,'big'))
        elif name.startswith('DUP'): code.append(127+int(name[3:]))
        elif name.startswith('SWAP'): code.append(143+int(name[4:]))
        else: code.append(INV[name])
    return bytes(code)

class VM:
    def __init__(self,code,stack,mem,pc=0,active=296):
        self.code=code; self.d=decode(code); self.s=list(stack); self.mem=bytearray(mem); self.pc=pc; self.active=active
        self.gas=0; self.steps=0; self.peak=len(stack); self.count=Counter(); self.writes=[]; self.reads=[]; self.max_access=0
    def expand(self,a,n):
        assert 0<=a<=100000 and n<=100000,('memory bound',a,n)
        if not n:return
        new=max(self.active,(a+n+31)//32)
        self.gas+=3*new+new*new//512-(3*self.active+self.active*self.active//512);self.active=new
        if len(self.mem)<a+n:self.mem.extend(bytes(a+n-len(self.mem)))
    def step(self):
        name,arg,nxt=self.d[self.pc]; oldpc=self.pc;self.pc=nxt; self.count[name]+=1;self.steps+=1
        s=self.s
        if name.startswith('PUSH'):
            s.insert(0,arg or 0); self.gas+=2 if name=='PUSH0' else 3
        elif name.startswith('DUP'):
            n=int(name[3:]);assert 1<=n<=16 and len(s)>=n
            self.max_access=max(self.max_access,n); s.insert(0,s[n-1]);self.gas+=3
        elif name.startswith('SWAP'):
            n=int(name[4:]);assert 1<=n<=16 and len(s)>n
            self.max_access=max(self.max_access,n+1);s[0],s[n]=s[n],s[0];self.gas+=3
        elif name=='POP':s.pop(0);self.gas+=2
        elif name in ('ADD','MUL','SUB','DIV','MOD','LT','GT','EQ','AND','OR','XOR','SHL','SHR','BYTE','EXP'):
            a=s.pop(0);b=s.pop(0)
            if name=='ADD':v=a+b
            elif name=='MUL':v=a*b
            elif name=='SUB':v=a-b
            elif name=='DIV':v=a//b if b else 0
            elif name=='MOD':v=a%b if b else 0
            elif name=='LT':v=int(a<b)
            elif name=='GT':v=int(a>b)
            elif name=='EQ':v=int(a==b)
            elif name=='AND':v=a&b
            elif name=='OR':v=a|b
            elif name=='XOR':v=a^b
            elif name=='SHL':v=(b<<a) if a<256 else 0
            elif name=='SHR':v=(b>>a) if a<256 else 0
            elif name=='BYTE':v=(b>>(8*(31-a)))&255 if a<32 else 0
            else:v=pow(a,b,B)
            self.gas+= (10+50*((b.bit_length()+7)//8)) if name=='EXP' else (5 if name in ('MUL','DIV','MOD') else 3)
            s.insert(0,v&MASK)
        elif name in ('MULMOD','ADDMOD'):
            a,b,m=s[:3];del s[:3];s.insert(0,((a*b if name=='MULMOD' else a+b)%m) if m else 0);self.gas+=8
        elif name in ('ISZERO','NOT'):
            a=s.pop(0);s.insert(0,int(a==0) if name=='ISZERO' else a^MASK);self.gas+=3
        elif name=='MLOAD':
            a=s.pop(0);self.expand(a,32);s.insert(0,int.from_bytes(self.mem[a:a+32],'big'));self.reads.append(a);self.gas+=3
        elif name=='MSTORE':
            a,v=s[:2];del s[:2];self.expand(a,32);self.mem[a:a+32]=v.to_bytes(32,'big');self.writes.append(a);self.gas+=3
        elif name=='CALLDATASIZE':s.insert(0,0);self.gas+=2
        elif name=='CALLDATACOPY':
            a,off,n=s[:3];del s[:3];self.expand(a,n);self.mem[a:a+n]=bytes(n);self.gas+=3+3*((n+31)//32)
        elif name=='MCOPY':
            dst,src,n=s[:3];del s[:3];self.expand(src,n);self.expand(dst,n)
            self.mem[dst:dst+n]=bytes(self.mem[src:src+n]);self.gas+=3+3*((n+31)//32)
            self.writes.extend(range(dst,dst+n,32));self.reads.extend(range(src,src+n,32))
        elif name in ('JUMP','JUMPI'):
            dst=s.pop(0);take=True if name=='JUMP' else bool(s.pop(0));self.gas+=8 if name=='JUMP' else 10
            if take:
                assert self.d[dst][0]=='JUMPDEST',('invalid jump',oldpc,dst);self.pc=dst
        elif name=='JUMPDEST':self.gas+=1
        elif name=='STOP':self.pc=len(self.code)
        else:raise AssertionError(('unsupported',oldpc,name))
        self.peak=max(self.peak,len(s));assert len(s)<=1024,('overflow',oldpc,len(s))
    def run(self,stops=(),max_steps=50000,min_steps=1):
        while self.pc<len(self.code) and (self.steps<min_steps or self.pc not in stops):
            assert self.steps<max_steps,('bounded steps',self.pc)
            self.step()
        return self
    def stats(self):return dict(gas=self.gas,steps=self.steps,peak=self.peak,max_access=self.max_access,loads=len(self.reads),stores=len(self.writes),active_words=self.active)

def word(mem,a,v):mem[a:a+32]=(v&MASK).to_bytes(32,'big')
def block(mem,a,v,n):mem[a:a+32*n]=v.to_bytes(32*n,'big')
def read(mem,a):return int.from_bytes(mem[a:a+32],'big')
def source():return bytes.fromhex(SOURCE.read_text().strip().removeprefix('0x'))
if __name__=='__main__':
    for pc,(name,arg,nxt) in decode(source()).items():
        if 1939<=pc<2470:print(pc,name,'' if arg is None else hex(arg))
