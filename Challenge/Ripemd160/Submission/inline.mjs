import {readFileSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import assert from 'node:assert/strict';
const prefix = 'Challenge/Ripemd160/Submission/';
const original = name => execFileSync('git', ['show', 'HEAD:' + prefix + name], {encoding:'utf8'});
const originalHex = original('bytecode.hex').trim();
const old = Buffer.from(originalHex, 'hex');
const source = original('Proofs/Bytecode/CachedMaskHoistInline.lean');
const spec = readFileSync(process.argv[2], 'utf8');
const table = name => spec.match(new RegExp('def ' + name + ' : Array \\w+ := #\\[([\\s\\S]*?)\\]'))[1].split(',').map(x=>Number(x.trim()));
const tables = {r:table('r'),rP:table('rP'),s:table('s'),sP:table('sP'),K:table('K'),KP:table('KP')};
const opcodes={MLOAD:0x51,ADD:1,MUL:2,AND:0x16,OR:0x17,XOR:0x18,NOT:0x19,SHR:0x1c,JUMP:0x56,JUMPDEST:0x5b,POP:0x50};
const push = (width,value) => ({width,value:String(value)});
const op = opcode => ({opcode});
const encode = instructions => Buffer.from(instructions.flatMap(x=>x.width===undefined?[x.opcode]:[0x5f+x.width,...Array.from({length:x.width},(_,i)=>Number((BigInt(x.value)>>BigInt(8*(x.width-i-1)))&255n))]));
const decode = bytes => {
  const out=[];
  for(let pc=0;pc<bytes.length;) {
    const opcode=bytes[pc], width=opcode>=0x60&&opcode<=0x7f?opcode-0x5f:0;
    out.push({...(opcode===0x5f?push(0,0):width?push(width,BigInt('0x'+bytes.subarray(pc+1,pc+1+width).toString('hex'))):op(opcode)),pc});
    pc+=width+1;
  }
  return out;
};
const originalInstructions=decode(old);
function quad(right,k) {
  const group=Math.floor(k/4), j=right?4-group:group, shift=right?5:0;
  const words=right?tables.rP:tables.r, rotations=right?tables.sP:tables.s;
  const vars={shift,constant:(right?tables.KP:tables.K)[group]};
  for(let i=0;i<4;i++){vars['p'+i]=644+4*words[4*k+i];vars['r'+i]=rotations[4*k+i];}
  const body=source.split(new RegExp('\\| '+(j===4?'_':j)+' =>'))[1].split(/\n  \| |\nset_option/)[0];
  const val=x=>{x=x.replaceAll('UInt256.ofNat','').replaceAll('shift.val','shift').replaceAll(/[()]/g,'').trim();const parts=x.split(/\s*([+-])\s*/);let n=vars[parts[0]]??Number(parts[0]);for(let i=1;i<parts.length;i+=2)n+=(parts[i]==='+'?1:-1)*(vars[parts[i+1]]??Number(parts[i+1]));assert(Number.isFinite(n),x);return n;};
  const out=[];
  for (const line of body.split('\n')) {
    let m;
    if(m=line.match(/\.push (\d+) (.*?)[,\]]?$/))out.push(push(Number(m[1]),val(m[2])));
    else if(m=line.match(/\.op \(\.(Dup|Swap) ⟨([^,]+)/))out.push(op((m[1]==='Dup'?0x80:0x90)+val(m[2])));
    else if(m=line.match(/\.op \.(\w+)/)){assert(m[1] in opcodes,m[1]);out.push(op(opcodes[m[1]]));}
  }
  assert(out.length>90&&out.length<130);
  return out;
}
const extra=[op(0x5b)];
const leftStart=old.length;
const quads=[];
function appendLane(right){for(let k=0;k<20;k++){const code=quad(right,k);quads.push({right,k,index:originalInstructions.length+extra.length,pc:old.length+encode(extra).length,code});extra.push(...code);}}
appendLane(false);
extra.push(push(2,originalInstructions[2142].pc),op(0x56));
const rightStart=old.length+encode(extra).length;
extra.push(op(0x5b));
appendLane(true);
extra.push(push(2,originalInstructions[2804].pc),op(0x56));
assert.equal(originalInstructions[907].value,'4');
originalInstructions[907].value=String(leftStart);
// Replace the wrapper with a direct bridge. Enlarge the next (unreachable)
// push to keep all subsequent original instruction indices and PCs stable.
originalInstructions[2154]=push(2,rightStart);
originalInstructions[2155]=op(0x56);
originalInstructions[2156].width=12;
const instructions=[...originalInstructions,...extra];
const hex=encode(instructions).toString('hex');
const layout={leftStart,rightStart,originalCount:originalInstructions.length,quads,instructions};
const patch=(name,data)=>'*** Add File: '+process.cwd()+'/'+prefix+name+'\n'+data.split('\n').map(l=>'+'+l).join('\n')+'\n';
console.log('*** Begin Patch\n'+patch('check/inline.hex',hex)+patch('check/inline-layout.json',JSON.stringify(layout))+'*** End Patch');
