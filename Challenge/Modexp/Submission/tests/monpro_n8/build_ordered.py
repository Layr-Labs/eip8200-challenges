"""Same n8 Montgomery mechanism, incumbent-ordered intermediate stores.
Build first in memory; --emit regenerates the canonical binding surfaces.
No compiler, scorer, external writes, or hosted submission.
"""
from pathlib import Path
import json, hashlib, re, sys
from evm import *
from schedule import Schedule
from mac_optimized import mac_keep_y
from c0_exact import c0
from test_current import source, BASE, S
FRAME=['pbi','pae','pbe','pd','ret']

def addcarry(q,a,b,lo,hi):
    q.arrange([a,b])
    for op in ['DUP2','ADD','DUP2','DUP2','LT','SWAP2','POP']:q.op(op)
    q.stack[:2]=[lo,hi]

def short(raw):
    ops=[]
    for pc,(op,arg,nxt) in decode(raw).items():
        if op.startswith('PUSH'):
            if arg==MASK:ops += [('PUSH',0),('NOT',None)]
            elif arg==MASK-31:ops += [('PUSH',31),('NOT',None)]
            else:ops.append(('PUSH',arg or 0))
        else:ops.append((op,None))
    return assemble(ops)

def row():
    q=Schedule(FRAME);bounds={}
    def mark(name):bounds[name]={'offset':len(short(q.bytes())),'stack':list(q.stack)}
    q.push(MASK,'K');q.dup('pae','ap');q.dup('pbi');q.op('MLOAD');q.label('bi');q.push(0,'ca')
    mark('l1_0')
    for j in range(8):
        q.load(8480-32*j,'t');q.dup('ap');q.push(32*(8-j));q.op('ADD');q.op('MLOAD');q.label('x')
        mac_keep_y(q,'x','bi','t','ca','u','ca');q.store('u',8480-32*j)
        mark('l1_'+str(j+1))
    q.drop('ap');q.drop('bi');q.load(8224,'tn');addcarry(q,'tn','ca','tn','upper')
    # These TWO stores, in this order, are exactly Monpro.midMem.
    q.store('tn',8224);q.store('upper',8192)
    mark('mid')
    q.load(8480,'u0');q.load(9376,'inv');q.binary('MUL','u0','inv','mu')
    q.load(224,'x');c0(q,'x','mu','cm');mark('l2_0')
    for k in range(7):
        q.load(8448-32*k,'u');q.load(192-32*k,'x')
        mac_keep_y(q,'x','mu','u','cm','v','cm');q.store('v',8480-32*k)
        mark('l2_'+str(k+1))
    q.drop('mu');q.load(8224,'tn');addcarry(q,'tn','cm','v7','upper2')
    # Match tailMem1 before loading T[9] for tailMem's second write.
    q.store('v7',8256);q.load(8192,'upper');q.binary('ADD','upper','upper2','v8');q.store('v8',8224)
    q.drop('K');q.arrange(FRAME);q.push(MASK-31);q.op('ADD');q.label('pbi')
    mark('tail')
    assert q.stack==FRAME
    return short(q.bytes()),bounds

def build():
    raw=source(BASE);b=bytearray(raw);labels={};fix=[]
    def emit(op,arg=None):b.extend(assemble([(op,arg)]))
    def label(name):labels[name]=len(b);emit('JUMPDEST')
    def dest(name):fix.append((len(b)+1,name));b.extend(bytes([97,0,0]))
    label('dispatch');b.extend(raw[1939:1974]);emit('PUSH',9344);emit('MLOAD')
    emit('DUP1');emit('PUSH',256);emit('EQ');dest('entry8');emit('JUMPI')
    emit('POP');emit('PUSH',1974);emit('JUMP');label('entry8');emit('POP');label('row8')
    body,bounds=row();start=len(b);b.extend(body)
    for name,x in bounds.items():x['pc']=start+x['offset']
    emit('DUP3');emit('DUP2');emit('GT');dest('row8');emit('JUMPI');b.extend(raw[2455:2462])
    for off,name in fix:b[off:off+2]=labels[name].to_bytes(2,'big')
    b[1939:1944]=b'\x5b\x61'+labels['dispatch'].to_bytes(2,'big')+b'\x56'
    return bytes(b),labels,bounds

def emit_bindings(code,labels,bounds):
    (S/'bytecode.hex').write_text(code.hex()+'\n')
    p=S/'Bytes.lean';header=p.read_text().split('private abbrev submissionChunk0')[0]
    chunks=[code[i:i+64] for i in range(0,len(code),64)];body=''
    for i,c in enumerate(chunks):
        body+=f'private abbrev submissionChunk{i} : ByteArray := ByteArray.mk #[\n'
        body+=',\n'.join('  '+', '.join(f'0x{v:02x}' for v in c[j:j+12]) for j in range(0,len(c),12))+'\n]\n\n'
    body+='abbrev submissionBytes : ByteArray :=\n  '+' ++\n  '.join(f'submissionChunk{i}' for i in range(len(chunks)))+'\n\n'
    body+=f'@[simp] theorem submissionBytes_size : submissionBytes.size = {len(code)} := by\n  decide\n\nend Challenge.Modexp\n';p.write_text(header+body)
    p=S/'Proofs/Bytecode/Artifact.lean';pre,rest=p.read_text().split('def submissionInstructions : List Instr :=',1);_,post=rest.split('theorem submissionInstructions_count',1)
    items=list(decode(code).items());lines=[]
    for pc,(name,arg,nxt) in items:
        if name.startswith('PUSH'):x=f'push {nxt-pc-1} {arg or 0}'
        elif name.startswith(('DUP','SWAP')):
            k=3 if name.startswith('DUP') else 4
            x='op (EvmSemantics.Operation.'+('Dup' if k==3 else 'Swap')+' { idx := '+str(int(name[k:])-1)+' })'
        else:x='op EvmSemantics.Operation.'+('INVALID' if name=='0xfe' else name)
        lines.append('YulEvmCompiler.Instr.'+x)
    post=re.sub(r'submissionInstructions.length = \d+',f'submissionInstructions.length = {len(lines)}',post,count=1)
    p.write_text(pre+'def submissionInstructions : List Instr :=\n['+',\n '.join(lines)+']\n\ntheorem submissionInstructions_count'+post)
    text='''import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Exact n8 paths. Execution/full-call integration is required separately. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.MonproN8
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
'''
    def located(i):
        pc,(name,arg,nxt)=items[i]
        if name.startswith('PUSH'):return f'pushAt {i} {nxt-pc-1} {arg or 0}'
        if name.startswith(('DUP','SWAP')):
            k=3 if name.startswith('DUP') else 4
            return f'opAt {i} (.'+('Dup' if k==3 else 'Swap')+' ⟨'+str(int(name[k:])-1)+', by decide⟩)'
        return f'opAt {i} .{name}'
    groups=[('entry',list(range(1379,1382)))]+[(f'append{k}',list(range(i,min(i+32,len(items))))) for k,i in enumerate(range(len(decode(source(BASE))),len(items),32))]
    for name,inds in groups:
        text+=f'\ndef {name} : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=\n  ['+',\n   '.join(located(i) for i in inds)+']\n'
        text+=f'theorem {name}_pc : Artifact.instructionPC {inds[0]} = {items[inds[0]][0]} := by rfl\n'
    for label,pc in labels.items():
        i=next(i for i,(p,_) in enumerate(items) if p==pc)
        text+=f'\ntheorem jump_{label} : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode {pc} = true :=\n  Artifact.isValidJumpDest_index {i} (by rfl)\n'
    text+='\nend Challenge.Modexp.Submission.Proofs.Fast.MonproN8\n'
    (S/'Proofs/Fast/MonproN8Paths.lean').write_text(text)
    identity={'base':BASE,'sha256':hashlib.sha256(code).hexdigest(),'bytes':len(code),'instructions':len(items),'labels':labels,'boundaries':bounds,'eligible':False}
    (Path(__file__).parent/'identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    return identity

if __name__=='__main__':
    from test_memory_order import check
    code,labels,bounds=build();print(json.dumps(check(code,labels['row8']),indent=2))
    if '--emit' in sys.argv:print(json.dumps(emit_bindings(code,labels,bounds),indent=2))
