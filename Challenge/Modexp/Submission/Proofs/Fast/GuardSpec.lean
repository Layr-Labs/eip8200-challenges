import Challenge.Modexp.Submission.Proofs.Fast.GuardLogic
import Challenge.Modexp.Submission.Proofs.Fast.RSACertificate

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardSpec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardData GuardLogic RSACertificate

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256)
    (hmem : (off, value) ∈ checks) :
    Precompile.bytesToNatPadded input off 32 = value.toNat := by
  rw [← Challenge.EvmProof.Bytes.readWord_toNat, hm.2 _ hmem]

theorem sizes {input : ByteArray} (hm : Matches input) :
    baseSize input = 256 ∧ exponentSize input = 3 ∧ modulusSize input = 256 := by
  have h0 := wordValue hm 0 256 (by simp [checks])
  have h32 := wordValue hm 32 3 (by simp [checks])
  have h64 := wordValue hm 64 256 (by simp [checks])
  change Precompile.bytesToNatPadded input 0 32 = 256 at h0
  change Precompile.bytesToNatPadded input 32 32 = 3 at h32
  change Precompile.bytesToNatPadded input 64 32 = 256 at h64
  exact ⟨h0, h32, h64⟩

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 256 = base := by
  have h0 := wordValue hm 96
    5204757502602156741860927903554486215631002020034533658579986437169090367113
    (by simp [checks])
  have h1 := wordValue hm 128
    63281855121729576028135952504278109029469994387028540079769462288734980692379
    (by simp [checks])
  have h2 := wordValue hm 160
    43955854185733434782678024279111821513371604761470886693064552075468003969770
    (by simp [checks])
  have h3 := wordValue hm 192
    85909128446909059588316066171361083131937545499049077817722168959598184821777
    (by simp [checks])
  have h4 := wordValue hm 224
    69825330230688921115527317574359630961253013696483226710135179334297009575826
    (by simp [checks])
  have h5 := wordValue hm 256
    19202660333895461906736249453977813469536985895555090982420583257661385454895
    (by simp [checks])
  have h6 := wordValue hm 288
    26054233372445659190091871567197130036051646819490296855113304995001464273605
    (by simp [checks])
  have h7 := wordValue hm 320
    76441194212611082221067249017375818798609081338753921089749826938651926500820
    (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 =
    5204757502602156741860927903554486215631002020034533658579986437169090367113 at h0
  change Precompile.bytesToNatPadded input 128 32 =
    63281855121729576028135952504278109029469994387028540079769462288734980692379 at h1
  change Precompile.bytesToNatPadded input 160 32 =
    43955854185733434782678024279111821513371604761470886693064552075468003969770 at h2
  change Precompile.bytesToNatPadded input 192 32 =
    85909128446909059588316066171361083131937545499049077817722168959598184821777 at h3
  change Precompile.bytesToNatPadded input 224 32 =
    69825330230688921115527317574359630961253013696483226710135179334297009575826 at h4
  change Precompile.bytesToNatPadded input 256 32 =
    19202660333895461906736249453977813469536985895555090982420583257661385454895 at h5
  change Precompile.bytesToNatPadded input 288 32 =
    26054233372445659190091871567197130036051646819490296855113304995001464273605 at h6
  change Precompile.bytesToNatPadded input 320 32 =
    76441194212611082221067249017375818798609081338753921089749826938651926500820 at h7
  rw [show 256 = 32 + 224 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 224 = 32 + 192 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 192 = 32 + 160 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 160 = 32 + 128 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  norm_num [base]

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 352 3 = 65537 := by
  have hw := wordValue hm 352
    452324521598467085373558698738785274637982913208579633907898081764202740992
    (by simp [checks])
  change Precompile.bytesToNatPadded input 352 32 =
    452324521598467085373558698738785274637982913208579633907898081764202740992 at hw
  rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 352 3 (by omega),
    Challenge.EvmProof.Bytes.readWord_toNat, hw]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 355 256 = modulus := by
  have hw352 := wordValue hm 352
    452324521598467085373558698738785274637982913208579633907898081764202740992
    (by simp [checks])
  change Precompile.bytesToNatPadded input 352 32 =
    452324521598467085373558698738785274637982913208579633907898081764202740992 at hw352
  have he := exponentValue hm
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 352 3 29
  have hfirst : Precompile.bytesToNatPadded input 355 29 =
      4771268853906436447103792735857560694584499449010242211731709068279040 := by
    norm_num at hsplit
    rw [hw352, he] at hsplit
    norm_num at hsplit
    omega
  have h1 := wordValue hm 384
    9627517346447367618050140505607668160680553384609730874378977357693307294624
    (by simp [checks])
  have h2 := wordValue hm 416
    23914626403865118422549393746198425187271253124650140704454329390959559138920
    (by simp [checks])
  have h3 := wordValue hm 448
    38311713511462522110458585356116005585671870710873149374701065632428634475996
    (by simp [checks])
  have h4 := wordValue hm 480
    48151510786387428585737698962956619369166187671466117465503171502731926895950
    (by simp [checks])
  have h5 := wordValue hm 512
    61739249361961769659166632957096972008755669043881026467845481882835731896669
    (by simp [checks])
  have h6 := wordValue hm 544
    92675087986974552283256406722435621174918856095734773600019478320879083557616
    (by simp [checks])
  have h7 := wordValue hm 576
    54145282474824214972220247004005524167635414539690773466529844265217144481216
    (by simp [checks])
  have hw608 := wordValue hm 608
    64827516786964288457452729860119806527709808231333806429784401219587764387840
    (by simp [checks])
  change Precompile.bytesToNatPadded input 384 32 =
    9627517346447367618050140505607668160680553384609730874378977357693307294624 at h1
  change Precompile.bytesToNatPadded input 416 32 =
    23914626403865118422549393746198425187271253124650140704454329390959559138920 at h2
  change Precompile.bytesToNatPadded input 448 32 =
    38311713511462522110458585356116005585671870710873149374701065632428634475996 at h3
  change Precompile.bytesToNatPadded input 480 32 =
    48151510786387428585737698962956619369166187671466117465503171502731926895950 at h4
  change Precompile.bytesToNatPadded input 512 32 =
    61739249361961769659166632957096972008755669043881026467845481882835731896669 at h5
  change Precompile.bytesToNatPadded input 544 32 =
    92675087986974552283256406722435621174918856095734773600019478320879083557616 at h6
  change Precompile.bytesToNatPadded input 576 32 =
    54145282474824214972220247004005524167635414539690773466529844265217144481216 at h7
  change Precompile.bytesToNatPadded input 608 32 =
    64827516786964288457452729860119806527709808231333806429784401219587764387840 at hw608
  have hlast : Precompile.bytesToNatPadded input 608 3 = 9392915 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 608 3 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, hw608]
    norm_num [Nat.shiftRight_eq_div_pow]
  rw [show 256 = 29 + 227 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 227 = 32 + 195 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 195 = 32 + 163 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 163 = 32 + 131 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 131 = 32 + 99 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 99 = 32 + 67 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 67 = 32 + 35 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [show 35 = 32 + 3 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num at hfirst h1 h2 h3 h4 h5 h6 h7 hlast ⊢
  rw [hfirst, h1, h2, h3, h4, h5, h6, h7, hlast]
  norm_num [modulus]

theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 256 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  rw [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.GuardSpec
