"""Generate bounded exact-byte n8 MAC trace contracts (no compiler)."""
from pathlib import Path
from build_ordered import build, S
from evm import decode
code,labels,bounds=build();items=list(decode(code).items())
assert code==bytes.fromhex((S/'bytecode.hex').read_text())
by_pc={pc:i for i,(pc,_) in enumerate(items)}

def located(i):
    pc,(op,arg,nxt)=items[i]
    if op.startswith('PUSH'):return f'pushAt {i} {nxt-pc-1} {arg or 0}'
    if op.startswith(('DUP','SWAP')):
        k=3 if op.startswith('DUP') else 4
        return f'opAt {i} (.'+('Dup' if k==3 else 'Swap')+' ⟨'+str(int(op[k:])-1)+', by decide⟩)'
    return f'opAt {i} .{op}'

head='''import Challenge.Modexp.Submission.Proofs.Fast.MonproN8Memory
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.MonproN8
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.EvmProof.Word

/-- A boundary changes only pc, memory and the explicitly listed stack. -/
def atState (s : State) (mem : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, memory := mem, stack := stk }

def l1Next (mem : ByteArray) (bi : UInt256) (pa j : Nat) (c : UInt256) : MacState :=
  let x := MachineState.readWord mem (pa + 32 * (7 - j))
  let t := MachineState.readWord mem (8256 + 32 * (7 - j))
  { memory := MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (macSum x bi t c).toNat 32) (8256 + 32 * (7 - j))
    carry := macCarry x bi t c }

def l2Next (mem : ByteArray) (mu : UInt256) (k : Nat) (c : UInt256) : MacState :=
  let x := MachineState.readWord mem (32 * (6 - k))
  let t := MachineState.readWord mem (8256 + 32 * (6 - k))
  { memory := MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (macSum x mu t c).toNat 32) (8256 + 32 * (7 - k))
    carry := macCarry x mu t c }

theorem l1Next_eq (mem : ByteArray) (bi : UInt256) (pa j : Nat) :
    l1Next (l1Step mem bi pa 8 j).memory bi pa j (l1Step mem bi pa 8 j).carry =
      l1Step mem bi pa 8 (j + 1) := by rfl

theorem l2Next_eq (mem : ByteArray) (mu c0 : UInt256) (k : Nat) :
    l2Next (l2Step mem mu c0 8 k).memory mu k (l2Step mem mu c0 8 k).carry =
      l2Step mem mu c0 8 (k + 1) := by rfl

'''
text=head
segments=[]
for phase,count in [('l1',8),('l2',7)]:
    for j in range(count):segments.append((f'{phase}_{j}',bounds[f'{phase}_{j}']['pc'],bounds[f'{phase}_{j+1}']['pc']))
segments += [('middle',bounds['l1_8']['pc'],bounds['mid']['pc']),('c0',bounds['mid']['pc'],bounds['l2_0']['pc']),('tail',bounds['l2_7']['pc'],bounds['tail']['pc'])]
for name,start,end in segments:
    inds=range(by_pc[start],by_pc[end])
    text+=f'def block_{name} : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=\n  ['+',\n   '.join(located(i) for i in inds)+']\n\n'
    text+=f'theorem pc_{name} : Artifact.instructionPC {by_pc[start]} = {start} := by rfl\n\n'

simpbase='''opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange'''

def boundsproof(addrs):
    out=''
    for i in range(1,11):out+=f'  have hc{i} : rest.length + {i} < 1024 := by omega\n'
    for k,a in enumerate(addrs):
        out+=f'  have ha{k} : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat ({a}) 32) = s.activeWords :=\n    activeWords_fix s _ 32 (by decide) (by omega) hact\n'
    return out

for phase,count in [('l1',8),('l2',7)]:
    for j in range(count):
        name=f'{phase}_{j}';start=bounds[name]['pc'];end=bounds[f'{phase}_{j+1}']['pc']
        if phase=='l1':
            args='(bi c : UInt256) (pa : Nat)';hyp='\n    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472)'
            stk='[c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest'
            call=f'l1Next mem bi pa {j} c'
            ostk=f'[{call}.carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest'
            # Parenthesize projections explicitly.
            ostk=f'[({call}).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest'
            addrs=[f'pa + {32*(7-j)}',str(8480-32*j)]
        else:
            args='(mu c : UInt256)';hyp=''
            stk='[c, mu, maxWord] ++ rest';call=f'l2Next mem mu {j} c';ostk=f'[({call}).carry, mu, maxWord] ++ rest'
            addrs=[str(192-32*j),str(8448-32*j),str(8480-32*j)]
        text+=f'''/-- Exact actual-byte {phase.upper()} MAC, with the entire suffix and memory. -/
theorem run_{name} (s : State) (mem : ByteArray) {args} (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat){hyp} :
    Challenge.EvmProof.Stepper.runLocatedBlock block_{name}
      (atState s mem {start} ({stk})) =
      some (atState s ({call}).memory {end} ({ostk})) := by
'''
        text+=boundsproof(addrs)
        extras=[]
        if phase=='l1':
            mod=2**256;off=32*(8-j);xoff=32*(7-j)
            text+=f'''  have hpaN : (pa - 32) % {mod} = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : ({off} + (pa - 32)) % {mod} = pa + {xoff} := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
'''
            extras=['hpaN','hxN']
        names=[f'hc{i}' for i in range(1,11)]+[f'ha{k}' for k in range(len(addrs))]+extras
        text+=f'''  simp (config := {{ maxSteps := 800000 }})
    [block_{name}, {simpbase}, {phase}Next, macSum, macCarry, mulHi,
      {', '.join(names)}]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

'''
text += '''theorem wordAddComm (x y : UInt256) : x + y = y + x := by
  apply word_ext
  simp only [word_toNat_add]
  rw [Nat.add_comm]

theorem wordMulComm (x y : UInt256) : x * y = y * x := by
  apply word_ext
  simp only [Monpro.word_toNat_mul]
  rw [Nat.mul_comm]

'''
for name,args,stk,memout,stkout,addrs,extra in [
    ('middle','(c bi ap : UInt256)',
     '[c, bi, ap, maxWord] ++ rest','midMem mem c','[maxWord] ++ rest',
     ['8224','8192'],'midMem, midMem1, wordAddComm'),
    ('c0','', '[maxWord] ++ rest','mem','[rowC0 mem 8, rowMu mem 8, maxWord] ++ rest',
     ['8480','9376','224'],'rowC0, rowMu, mulHi, wordMulComm, MacAlt.subSubFold'),
    ('tail','(c mu pbi : UInt256)', '[c, mu, maxWord, pbi] ++ rest',
     'tailMem mem c',
     '[UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest',
     ['8224','8256','8192'],'tailMem, tailMem1, wordAddComm')]:
    _,start,end=next(x for x in segments if x[0]==name)
    text+=f'''/-- Exact {name} boundary; complete scratch and frame are retained. -/
theorem run_{name} (s : State) (mem : ByteArray) {args} (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_{name}
      (atState s mem {start} ({stk})) =
      some (atState s ({memout}) {end} ({stkout})) := by
'''
    text+=boundsproof(addrs)
    names=[f'hc{i}' for i in range(1,11)]+[f'ha{k}' for k in range(len(addrs))]
    text+=f'''  simp (config := {{ maxSteps := 800000 }})
    [block_{name}, {simpbase}, {extra}, {', '.join(names)}]

'''
text += '''/-- One full arithmetic row: all eight L1 steps, exact midMem,
seven L2 steps and exact tailMem. The caller suffix is unchanged, and the
outer pointer is decremented. No reducedness or inverse premise is used. -/
def gasSteps_rowArithmetic (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pbi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1012) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (atState s mem 5414
        ([UInt256.ofNat 0, rowBi mem pb 8 i, UInt256.ofNat (pa - 32), maxWord, pbi] ++ rest))
      (atState s (rowMem mem pa pb 8 i) 6083
        ([UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest)) := by
  let bi := rowBi mem pb 8 i
  let suffix := pbi :: rest
  have hcap' : suffix.length ≤ 1013 := by simp only [suffix, List.length_cons]; omega
'''
for j in range(8):
    start=bounds[f'l1_{j}']['pc']
    st=f'atState s (l1Step mem bi pa 8 {j}).memory {start} ([(l1Step mem bi pa 8 {j}).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)'
    text+=f'''  have hL1_{j} := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := {st}) Artifact.submissionArtifact .Osaka block_l1_{j} hcode hfork
    (run_l1_{j} s (l1Step mem bi pa 8 {j}).memory bi (l1Step mem bi pa 8 {j}).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_{j}
'''
text+='''  let first := l1Step mem bi pa 8 8
  let middle := midMem first.memory first.carry
  have hMid := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s first.memory 5735
      ([first.carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix))
    Artifact.submissionArtifact .Osaka block_middle hcode hfork
    (run_middle s first.memory first.carry bi (UInt256.ofNat (pa - 32)) suffix hcap' hrun hact) hrun hnp
  have hC0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s middle 5757 ([maxWord] ++ suffix))
    Artifact.submissionArtifact .Osaka block_c0 hcode hfork
    (run_c0 s middle suffix hcap' hrun hact) hrun hnp
  have hmu : rowMu middle 8 = rowMu first.memory 8 := rowMu_midMem8 _ _
  have hc0 : rowC0 middle 8 = rowC0 first.memory 8 := rowC0_midMem8 _ _
  rw [hmu, hc0] at hC0
  let mu := rowMu first.memory 8
  let c0 := rowC0 first.memory 8
'''
for j in range(7):
    start=bounds[f'l2_{j}']['pc']
    st=f'atState s (l2Step middle mu c0 8 {j}).memory {start} ([(l2Step middle mu c0 8 {j}).carry, mu, maxWord] ++ suffix)'
    text+=f'''  have hL2_{j} := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := {st}) Artifact.submissionArtifact .Osaka block_l2_{j} hcode hfork
    (run_l2_{j} s (l2Step middle mu c0 8 {j}).memory mu (l2Step middle mu c0 8 {j}).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_{j}
'''
text+='''  let second := l2Step middle mu c0 8 7
  have hTail := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s second.memory 6052 ([second.carry, mu, maxWord, pbi] ++ rest))
    Artifact.submissionArtifact .Osaka block_tail hcode hfork
    (run_tail s second.memory second.carry mu pbi rest (by omega) hrun hact) hrun hnp
  exact ''' + '.trans ('.join([f'hL1_{j}' for j in range(8)]+['hMid','hC0']+[f'hL2_{j}' for j in range(7)]+['hTail']) + ')' * 17 + '\n\n'
text+='end Challenge.Modexp.Submission.Proofs.Fast.MonproN8\n'
(S/'Proofs/Fast/MonproN8Mac.lean').write_text(text)
print({'generated_mac_contracts':15,'located_blocks':len(segments),'bytes':len(text.encode()),'compiled':False})
