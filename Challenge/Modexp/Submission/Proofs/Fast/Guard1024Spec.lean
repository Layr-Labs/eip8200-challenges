import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Logic
import Challenge.Modexp.Submission.Proofs.Fast.RSA1024Certificate

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Guard1024Data Guard1024Logic RSA1024Certificate

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256)
    (hmem : (off, value) ∈ checks) :
    Precompile.bytesToNatPadded input off 32 = value.toNat := by
  rw [← Challenge.EvmProof.Bytes.readWord_toNat, hm.2 _ hmem]

theorem sizes {input : ByteArray} (hm : Matches input) :
    baseSize input = 128 ∧ exponentSize input = 1 ∧ modulusSize input = 128 := by
  have h0 := wordValue hm 0 128 (by simp [checks])
  have h32 := wordValue hm 32 1 (by simp [checks])
  have h64 := wordValue hm 64 128 (by simp [checks])
  change Precompile.bytesToNatPadded input 0 32 = 128 at h0
  change Precompile.bytesToNatPadded input 32 32 = 1 at h32
  change Precompile.bytesToNatPadded input 64 32 = 128 at h64
  exact ⟨h0, h32, h64⟩

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 128 = base := by
  have h0 := wordValue hm 96
    8793306660163990040561289890486148164325486782586370684446629828706317024479
    (by simp [checks])
  have h1 := wordValue hm 128
    44513626964103848159171604930358580559684327884685485523541937090475774086062
    (by simp [checks])
  have h2 := wordValue hm 160
    13735552034596734314392003083933777828981134616265434527816408455772068535085
    (by simp [checks])
  have h3 := wordValue hm 192
    20741756277002281002578156983727958327059860011036567020672535493562176622834
    (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 =
    8793306660163990040561289890486148164325486782586370684446629828706317024479 at h0
  change Precompile.bytesToNatPadded input 128 32 =
    44513626964103848159171604930358580559684327884685485523541937090475774086062 at h1
  change Precompile.bytesToNatPadded input 160 32 =
    13735552034596734314392003083933777828981134616265434527816408455772068535085 at h2
  change Precompile.bytesToNatPadded input 192 32 =
    20741756277002281002578156983727958327059860011036567020672535493562176622834 at h3
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num at h0 h1 h2 h3 ⊢
  rw [h0, h1, h2, h3]
  norm_num [base]

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 224 1 = 3 := by
  have hw := wordValue hm 224
    1669349634595236858291517537149291117455193199261270936918514663252800326893
    (by simp [checks])
  change Precompile.bytesToNatPadded input 224 32 =
    1669349634595236858291517537149291117455193199261270936918514663252800326893 at hw
  rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 224 1 (by omega),
    Challenge.EvmProof.Bytes.readWord_toNat, hw]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 225 128 = modulus := by
  have hw224 := wordValue hm 224
    1669349634595236858291517537149291117455193199261270936918514663252800326893
    (by simp [checks])
  change Precompile.bytesToNatPadded input 224 32 =
    1669349634595236858291517537149291117455193199261270936918514663252800326893 at hw224
  have he := exponentValue hm
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 224 1 31
  have hfirst : Precompile.bytesToNatPadded input 225 31 =
      312411088845437693171545056578729697299685566460795577081121100660068338925 := by
    norm_num at hsplit
    rw [hw224, he] at hsplit
    norm_num at hsplit
    omega
  have h1 := wordValue hm 256
    99117046946972186913022966043064609353311784182601608842001214174495081049617
    (by simp [checks])
  have h2 := wordValue hm 288
    33420266142682261421808456191225212768240439756117012645431084487760459509359
    (by simp [checks])
  have h3 := wordValue hm 320
    63069685324986315081589603195175474010237415761785462502555456014205811395170
    (by simp [checks])
  have hw352 := wordValue hm 352
    28495709460745782467519422091981789823265660288809982556585264814447371747328
    (by simp [checks])
  change Precompile.bytesToNatPadded input 256 32 =
    99117046946972186913022966043064609353311784182601608842001214174495081049617 at h1
  change Precompile.bytesToNatPadded input 288 32 =
    33420266142682261421808456191225212768240439756117012645431084487760459509359 at h2
  change Precompile.bytesToNatPadded input 320 32 =
    63069685324986315081589603195175474010237415761785462502555456014205811395170 at h3
  change Precompile.bytesToNatPadded input 352 32 =
    28495709460745782467519422091981789823265660288809982556585264814447371747328 at hw352
  have hlast : Precompile.bytesToNatPadded input 352 1 = 63 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 352 1 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, hw352]
    norm_num [Nat.shiftRight_eq_div_pow]
  rw [show 128 = 31 + 97 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 97 = 32 + 65 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 65 = 32 + 33 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 33 = 32 + 1 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num at hfirst h1 h2 h3 hlast ⊢
  rw [hfirst, h1, h2, h3, hlast]
  norm_num [modulus]

theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 128 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  rw [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Spec
