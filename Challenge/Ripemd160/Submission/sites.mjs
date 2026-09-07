import {readFileSync} from 'node:fs';
const root='Challenge/Ripemd160/Submission/';
const x=JSON.parse(readFileSync(root+'check/inline-layout.json'));
let s=`import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open CavityQuadGroup StackRoundTemplate
abbrev A := Artifact.submissionArtifact
theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide
theorem pc_toNat (index : Nat) :
    (UInt256.ofNat (A.instructionPC index)).toNat = A.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (A.instructionPC_le_code_size index) code_bound)
private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index
`;
for(const side of ['left','right']){
const qs=x.quads.filter(q=>q.right===(side==='right'));const shift=side==='left'?0:5;
for(const q of qs){s+=`
def ${side}${q.k} : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.${side} ${q.k}) ${shift}) :=
  StackSiteBuilder.ofSlice _ ${q.index} (by rfl) (by
    change ${q.index} + (CachedMaskQuadGroup.code (FullInlineParams.${side} ${q.k}) ${shift}).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)
`;}
s+=`\ndef ${side} (k : Fin 20) : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.${side} k) ${shift}) :=
  match k with\n`+qs.map(q=>`  | ⟨${q.k}, _⟩ => ${side}${q.k}`).join('\n')+'\n  | ⟨n + 20, h⟩ => False.elim (by omega)\n';
s+=`def ${side}PC (n : Nat) : UInt256 := match n with\n`+qs.map(q=>`  | ${q.k} => ${q.pc}`).join('\n')+`\n  | _ => ${qs[19].pc+qs[19].code.reduce((n,i)=>n+(i.width===undefined?1:i.width+1),0)}\n`;
s+=`theorem ${side}_start (k : Fin 20) : (${side} k).startPC = ${side}PC k.val := by
  fin_cases k
${qs.map(q=>`  · change UInt256.ofNat (A.instructionPC ${q.index}) = UInt256.ofNat ${q.pc}\n    rw [ArtifactByteLength.instructionPC_eq_byteLength]\n    rfl`).join('\n')}
theorem ${side}_end (k : Fin 20) : (${side} k).endPC = ${side}PC (k.val + 1) := by
  fin_cases k
${qs.map(q=>`  · change UInt256.ofNat (A.instructionPC ${q.index+q.code.length}) = UInt256.ofNat ${q.pc+q.code.reduce((n,i)=>n+(i.width===undefined?1:i.width+1),0)}\n    rw [ArtifactByteLength.instructionPC_eq_byteLength]\n    rfl`).join('\n')}
`;
}
const lastl=x.quads[19],lastr=x.quads[39];
for(const [name,p,j,d] of [['leftEntry',907,908,x.originalCount],['rightEntry',2154,2155,lastl.index+lastl.code.length+2],['leftReturn',lastl.index+lastl.code.length,lastl.index+lastl.code.length+1,2142],['rightReturn',lastr.index+lastr.code.length,lastr.index+lastr.code.length+1,2804]]){
const target=x.instructions[p].value;
s+=`\ndef ${name} : Bridge A .Osaka where
  push := exactSite ${p} (.push 2 ${target}) (by rfl) (by decide)
  jump := exactSite ${j} (.op .JUMP) (by rfl) ⟨by decide, trivial, rfl⟩
  destination := exactSite ${d} (.op .JUMPDEST) (by rfl) ⟨by decide, trivial, rfl⟩
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
`;
}
s+='\nend Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites\n';
const mappings=[];
// Keep the expensive concrete-slice certificates separate from the small table.
s=s.replace(/def (left|right) \(k : Fin 20\)[\s\S]*?(?=\ndef (?:right0|leftEntry))/g,m=>{mappings.push(m);return '';});
if(mappings.length!==2)throw Error('mapping sections');
const table=`import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSiteData
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTemplate
${mappings.join('\n')}
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
`;
const patch=(name,t)=>'*** Add File: '+process.cwd()+'/'+root+'Proofs/Bytecode/'+name+'\n'+t.trimEnd().split('\n').map(l=>'+'+l).join('\n')+'\n';
console.log('*** Begin Patch\n'+patch('FullInlineSiteData.lean',s)+patch('FullInlineSites.lean',table)+'*** End Patch');
