import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Exact-bytecode correctness for the direct stack-resident compressor. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode := by
  change Challenge.Ripemd160.Correct Challenge.Ripemd160.submissionBytecode
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard.correct_of_recognition
    Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_entry

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- executable 1e4024bf3f5b0b95a3375c21c2e8dccd5b51ebcc5e9b17ac606e490e5acb85bc, 5212 bytes,
-- 660772 gas at corpus seeds 0..2, 8174 units of the 8194 literal-encoding budget. Derived from
-- the 661024 image (5214 bytes, one step above): at both round changes that dropped the old key
-- with `SWAPa POP PUSH22 K SWAPb` (rounds 29 and 45), the previous round now pushes the new key
-- itself and swaps it into the old key's slot (`PUSH22 K SWAPn ADD` instead of `DUPn ADD`), so
-- the round-change prefix shrinks to `SWAPa SWAPb`; the boundary shape carries the key as
-- `.literal K`. -2 gas per site per block (2 x 63 x 2 = -252). 3677 instructions.
-- model Claude Opus 5.5, harness Claude Code.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one.
-- executable 6c83026f03003e9be4c0786fb485d5eee637c2dbcecd6b2bbd15a5379c0b7ec3, 5214 bytes,
-- 661024 gas at corpus seeds 0..2, 8182 units of the 8194 literal-encoding budget. Derived from
-- the promoted 522f1bcb image (5215 bytes, 661150 gas): round 76 consumes its dead `.pair` lane
-- mask in place (`DUP11 SWAP4 AND` instead of `DUP4 AND`, leaving a copy of `.factor` in that
-- slot), so the unpack becomes `SWAP8 SWAP3 DUP10 SWAP5 POP` and already supplies the factor copy
-- that round 77 used to `DUP10`: net -1 instruction and -2 gas per block (x 63 blocks = -126).
-- 3679 instructions; pcs >= 4478 move by +1 up to 4485, pcs >= 4522 by -1.
-- model Claude Opus 5.5, harness Claude Code.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one.
-- executable d13618dbd733a6c2ab9f681ad64d832dbc88cc487e49e8a30835c4a661ad8000, 5215 bytes,
-- 661150 gas at corpus seeds 0..2, 8181 units of the 8194 literal-encoding budget. Derived from
-- the promoted c19d26e2 image (5212 bytes, 661192 gas): the terminal round's `DUP5 AND` lane
-- mask (63 runs) is deleted and the schedule builder instead clears table byte 610 once per data
-- block with `PUSH0 PUSH2 0x262 MSTORE8` (42 runs), so the unmasked terminal word stays below
-- 2^120 in its lower half. 3680 instructions; pcs >= 858 move by +5, >= 4463 by +3.
-- model Claude Opus 5.5, harness Claude Code.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one.
-- executable 57759249fb656d26d3f1caef776f3cae7dacf700193d47cdee3322937ddac9e6, 5212 bytes,
-- 661512 gas at corpus seeds 0..2, 8182 units of the 8194 literal-encoding budget. Derived from
-- 02483f1554b094391c5803025591d9f8fc296350dd34bf7f9641cf922d235d73 (5212 bytes, 661704 gas): the
-- setup's modulus word (2^65+1)*2^144 is pushed as a PUSH27 literal instead of PUSH9/PUSH1/SHL,
-- paid with fifteen over-wide push-padding bytes (pc 232 and the schedule builder).
-- 3683 instructions; jump destinations 343, 301, 329, 471, 508 move; pcs from 860 on unchanged.
-- model Claude Opus 5, harness Claude Code.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one. Provenance and attribution have not been touched here.
-- executable 02483f1554b094391c5803025591d9f8fc296350dd34bf7f9641cf922d235d73, 5212 bytes,
-- 661704 gas at corpus seeds 0..2. Derived from
-- 592f0bb0ed6a9c7d15003049c02929b346a1b137c81c649b9a18c5d8ea3d0fe7 (5212 bytes, 661914 gas): the
-- schedule scratch is restaged as one store per half (high at 162, low at 252) and four 16-byte
-- MCOPYs, and schedule word 6 loses its mask (only word 11 stays masked). The proof evaluates the
-- clean reference over a zeroed-memory copy and keeps its own zero set, so lowClear and GapClear
-- are retired; the pad-only table agrees with its model from byte 28.
-- 3685 instructions; bytes 333, 337 and 506..738 differ; lanes and the terminal slot unchanged.
-- model Claude Opus 5, harness Claude Code.
-- executable 592f0bb0ed6a9c7d15003049c02929b346a1b137c81c649b9a18c5d8ea3d0fe7, 5212 bytes,
-- 661914 gas at corpus seeds 0..2, 8180 units of the 8194 literal-encoding budget. Derived from
-- 815073da176a6ee327fb5cff48b9e268def819556d9208f24bf083127cb09820 (5212 bytes, 662418 gas): the
-- schedule scratch is restaged as one store plus two 16-byte MCOPYs per half (high at 28, low at
-- 616), so every load keeps a zero byte between its lanes and only words 6 and 11 stay masked.
-- 3687 instructions; bytes 333, 337 and 506..857 differ; lanes and the terminal slot unchanged.
-- model Claude Opus 5, harness Claude Code.
-- executable 815073da176a6ee327fb5cff48b9e268def819556d9208f24bf083127cb09820, 5212 bytes,
-- 662418 gas at corpus seeds 0..2, 8180 units of the 8194 literal-encoding budget. Derived from
-- 87b2202df9e69ecd0fc6c4d7cc1aa64c8bebac4989adccb2a978371b576c481a (5212 bytes, 663258 gas):
-- the schedule builder makes its third staging copy with MCOPY(0xa <- 0x1c, 16) instead of a
-- store and stores the four diagonal words (0..3) unmasked; only words 4, 5, 6, 7 and 11 keep
-- the two-lane mask. Lanes and the terminal slot are byte-identical to the predecessor; the
-- unmasked words leave message bytes only between the lanes, where every paired read keeps a
-- provably-zero byte (PoolCertificatesV2.slack_sources). 3692 instructions (nine fewer), bytes
-- 549..772 differ, every program counter outside the window is unchanged.
-- model Claude Opus 5, harness Claude Code.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one. Provenance and attribution have not been touched here.
-- executable edd78ac56ece15e4283762b16ff54409cb244adb6dec492dc5d609e34a37c604, 5212 bytes,
-- 663636 gas at corpus seed 0, 8187 units of the 8194 literal-encoding budget. Derived from
-- 124d01057f5628e32d5d539622bf89afd5fc56287d8718d300eefa534d4a2842 (5212 bytes, 663683 gas) by
-- deleting three unreachable JUMPDESTs. Every JUMP and JUMPI in that image is immediately
-- preceded by a literal PUSH, so the set of reachable jump destinations is statically complete;
-- the JUMPDESTs at offsets 142, 143 and 225 are named by no PUSH immediate and are therefore
-- pure fall-through cost, executed 14, 14 and 19 times respectively over the scored corpus, 47
-- gas in total. Each freed byte is returned by widening a later PUSH: PUSH1 0xfb at offset 146
-- becomes PUSH3 0x0000fb and PUSH1 0x03 at offset 233 becomes PUSH2 0x0003. A PUSH costs three
-- gas at every width and zero-extension does not change the pushed value, so the compensation is
-- free. The length stays 5212, so the trailing 280-byte digest table keeps its CODESIZE-relative
-- position; 14 bytes differ, all inside offsets 142..146 and 225..233, and every program counter
-- outside those two windows is unchanged. Two further unreachable JUMPDESTs, at offsets 5086 and
-- 5152, lie inside that digest table: they are data rather than code, are never executed, and are
-- left untouched. The instruction list goes from 3706 to 3703 entries, so indices shift by 0
-- below 89, by -2 over 91..132 and by -3 from 142 up; the code region remains 4932 bytes.
--
-- NOTE FOR THE FILER: every line below this point was inherited with the base tree and describes
-- an EARLIER artifact, not this one. Provenance and attribution have not been touched here.
-- redraw marker 2026-09-15T09:15:23Z
-- Yukon reuse by @i34-9: source @ercumentyildirim, submission b6cd6b15-6fe8-48e2-bf2d-18d7d4b77aa9, commit ef17a52c1.
-- provenance marker RIPC0-30e4ab42-v1
-- base is NOT our work: submission b6cd6b15-6fe8-48e2-bf2d-18d7d4b77aa9, executable cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004, 5212 bytes, 664022 gas.
-- predecessor cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004, 5212 bytes, 664022 gas.
-- executable 30e4ab4256a50425c21370d99efee74f8f942e1265fa23a0c751b68f4cf39189, 5212 bytes, 664008 gas, 8187 units of the 8194 budget, derived from cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004 at 664022 gas by a single change. The predecessor line deletes an eagerly-built recogniser constant and leaves a one-byte JUMPDEST at offset 138 as padding; that JUMPDEST is dead. No PUSH immediate names offset 138, and every JUMP and JUMPI in the artifact is immediately preceded by a literal PUSH, so the set of reachable jump targets is statically complete and does not contain it. It is therefore pure fall-through cost, one gas on each of the fourteen scored vectors that reach the ordinary path. Deleting it frees one byte, which is returned by widening the PUSH2 0x00fb at offset 141 to PUSH3 0x0000fb: a PUSH costs three gas at every width and the pushed value is unchanged. The length stays 5212, so the digest table keeps its CODESIZE-relative position, and every instruction from offset 144 onward keeps its exact program counter. Three bytes differ from the predecessor.
-- model Claude Opus 5 (1M context), harness Claude Code.
