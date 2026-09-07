import {readFileSync} from 'node:fs';
const path='Challenge/Ripemd160/Submission/Proofs/Bytecode/CachedMaskLane.lean';
const layout=JSON.parse(readFileSync('Challenge/Ripemd160/Submission/check/inline-layout.json'));
let s=`import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackCompression QuadSemantic StackRoundTemplate StackRoundTrace CavityQuadGroup
open FullInlineParams (left4 right4)
open QuadRoundTemplate (factor)
abbrev Artifact := FullInlineSites.A
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt
abbrev stateAt := CavityQuadGroup.stateAt
`;
for(const side of ['left','right']){
const r=side==='right',args=r?' (a b c d e : UInt256)':'', pass=r?' a b c d e':'',tail=r?'a :: b :: c :: d :: e :: mask :: rho':'mask :: rho',cap=r?1001:1006,shift=r?5:0;
const first=layout.quads[r?20:0],last=layout.quads[r?39:19],ret=last.index+last.code.length,end=last.pc+last.code.reduce((n,i)=>n+(i.width===undefined?1:i.width+1),0),dest=r?2804:2142;
s+=`
private theorem ${side}_entry_end : FullInlineSites.${side}Entry.destination.pc.succ = FullInlineSites.${side}PC 0 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC ${first.index-1})).succ = UInt256.ofNat ${first.pc}
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem ${side}_return_start : FullInlineSites.${side}Return.push.pc = FullInlineSites.${side}PC 20 := by
  change UInt256.ofNat (FullInlineSites.A.instructionPC ${ret}) = UInt256.ofNat ${end}
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem ${side}_return_end : FullInlineSites.${side}Return.destination.pc.succ = QuadLayout.${side}PC 20 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC ${dest})).succ = UInt256.ofNat (FullInlineSites.A.instructionPC ${dest+1})
  repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private noncomputable def ${side}_quad (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking)${args} (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < ${cap}) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (FullInlineSites.${side}PC k.val) w (${tail}))
      (stateAt s (FullInlineSites.${side}PC (k.val + 1)) (${side}4 word k w) (${tail})) := by
  let site := FullInlineSites.${side} k
  have raw := CachedMaskQuadGroup.run_${side} (FullInlineParams.${side} k) s site.startPC w${pass} rho
    (FullInlineParams.${side}_fits s k hactive) hstack hrun
  rw [← CavityFragmentChain.site_end site, FullInlineParams.${side}_apply s word w k hwords] at raw
  have g : GasSteps (stateAt s site.startPC w (${tail}))
      (stateAt s site.endPC (${side}4 word k w) (${tail})) := by
    apply Stepper.runLocatedBlock_sound Artifact .Osaka site.path
    · exact hcode
    · exact hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw site (CachedMaskQuadGroup.advances (FullInlineParams.${side} k) ${shift})
        (stateAt s site.startPC w (${tail})) rfl]
      exact raw
    · exact hrun
    · exact hnp
  simpa only [site, FullInlineSites.${side}_start, FullInlineSites.${side}_end] using g

noncomputable def gasSteps_${side}80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking)${args} (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < ${cap}) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.${side}PC 0) working (${tail}))
      (stateAt s (QuadLayout.${side}PC 20) (${side}Rounds word 80 working) (${tail})) := by
  let states := fun n => stateAt s (FullInlineSites.${side}PC n)
    (${side}Rounds word (4 * n) working) (${tail})
  have step (i : Nat) (hi : i < 20) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := ${side}_quad s word (${side}Rounds word (4 * i) working)${pass} rho k
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : ${side}Rounds word (4 * (i + 1)) working =
        ${side}4 word k (${side}Rounds word (4 * i) working) := by
      rw [${side}Rounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (FullInlineSites.${side}PC (i + 1))
          (${side}4 word k (${side}Rounds word (4 * i) working)) (${tail}) =
        stateAt s (FullInlineSites.${side}PC (i + 1))
          (${side}Rounds word (4 * (i + 1)) working) (${tail})
      rw [hnext]
  have core := GasSteps.iterateBounded 20 step
  have hcap (w : Compression.EvmWorking) :
      ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (${tail})).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge FullInlineSites.${side}Entry s
    ([working.a, working.b, working.c, working.d, working.e] ++ factor :: (${tail}))
    (hcap working) hcode hfork hrun hnp
  let finish := ${side}Rounds word 80 working
  have leave := gasSteps_bridge FullInlineSites.${side}Return s
    ([finish.a, finish.b, finish.c, finish.d, finish.e] ++ factor :: (${tail}))
    (hcap finish) hcode hfork hrun hnp
  rw [${side}_entry_end] at enter
  rw [${side}_return_start, ${side}_return_end] at leave
  exact (enter.trans core).trans leave
`;
}
s+='\n#print axioms gasSteps_left80\n#print axioms gasSteps_right80\nend Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane\n';
console.log('*** Begin Patch\n*** Update File: '+process.cwd()+'/'+path+'\n@@\n'+readFileSync(path,'utf8').trimEnd().split('\n').map(l=>'-'+l).join('\n')+'\n'+s.trimEnd().split('\n').map(l=>'+'+l).join('\n')+'\n*** End Patch');
