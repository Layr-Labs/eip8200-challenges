import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Checks4

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk : List Nat :=
  (walk00 ++ (walk01 ++ (walk02 ++ (walk03 ++ (walk04 ++ (walk05 ++ (walk06 ++ (walk07 ++ (walk08 ++ (walk09 ++ (walk10 ++ (walk11 ++ (walk12 ++ (walk13 ++ (walk14 ++ (walk15 ++ (walk16 ++ (walk17 ++ (walk18 ++ (walk19 ++ (walk20 ++ (walk21 ++ (walk22 ++ (walk23 ++ (walk24 ++ (walk25 ++ (walk26 ++ (walk27 ++ (walk28 ++ (walk29 ++ (walk30 ++ (walk31 ++ (walk32 ++ (walk33 ++ (walk34 ++ (walk35 ++ (walk36 ++ (walk37 ++ (walk38 ++ (walk39 ++ (walk40 ++ (walk41 ++ (walk42 ++ (walk43 ++ (walk44 ++ (walk45 ++ (walk46 ++ (walk47 ++ (walk48 ++ (walk49 ++ (walk50 ++ (walk51 ++ (walk52 ++ (walk53 ++ (walk54 ++ (walk55 ++ (walk56 ++ (walk57 ++ (walk58 ++ (walk59 ++ (walk60 ++ (walk61 ++ (walk62 ++ (walk63 ++ (walk64 ++ (walk65 ++ (walk66 ++ (walk67 ++ walk68))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem completePath : ScanPath code 0 walk code.size := by
  rw [size_eq]
  exact (ScanPath.append path00 (ScanPath.append path01 (ScanPath.append path02 (ScanPath.append path03 (ScanPath.append path04 (ScanPath.append path05 (ScanPath.append path06 (ScanPath.append path07 (ScanPath.append path08 (ScanPath.append path09 (ScanPath.append path10 (ScanPath.append path11 (ScanPath.append path12 (ScanPath.append path13 (ScanPath.append path14 (ScanPath.append path15 (ScanPath.append path16 (ScanPath.append path17 (ScanPath.append path18 (ScanPath.append path19 (ScanPath.append path20 (ScanPath.append path21 (ScanPath.append path22 (ScanPath.append path23 (ScanPath.append path24 (ScanPath.append path25 (ScanPath.append path26 (ScanPath.append path27 (ScanPath.append path28 (ScanPath.append path29 (ScanPath.append path30 (ScanPath.append path31 (ScanPath.append path32 (ScanPath.append path33 (ScanPath.append path34 (ScanPath.append path35 (ScanPath.append path36 (ScanPath.append path37 (ScanPath.append path38 (ScanPath.append path39 (ScanPath.append path40 (ScanPath.append path41 (ScanPath.append path42 (ScanPath.append path43 (ScanPath.append path44 (ScanPath.append path45 (ScanPath.append path46 (ScanPath.append path47 (ScanPath.append path48 (ScanPath.append path49 (ScanPath.append path50 (ScanPath.append path51 (ScanPath.append path52 (ScanPath.append path53 (ScanPath.append path54 (ScanPath.append path55 (ScanPath.append path56 (ScanPath.append path57 (ScanPath.append path58 (ScanPath.append path59 (ScanPath.append path60 (ScanPath.append path61 (ScanPath.append path62 (ScanPath.append path63 (ScanPath.append path64 (ScanPath.append path65 (ScanPath.append path66 (ScanPath.append path67 path68))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem equalHits : targets reference StaticDomainFrontier64.pcs = targets code walk := by
  simp only [StaticDomainFrontier64.pcs, walk, targets_append, hits00, hits01, hits02, hits03, hits04, hits05, hits06, hits07, hits08, hits09, hits10, hits11, hits12, hits13, hits14, hits15, hits16, hits17, hits18, hits19, hits20, hits21, hits22, hits23, hits24, hits25, hits26, hits27, hits28, hits29, hits30, hits31, hits32, hits33, hits34, hits35, hits36, hits37, hits38, hits39, hits40, hits41, hits42, hits43, hits44, hits45, hits46, hits47, hits48, hits49, hits50, hits51, hits52, hits53, hits54, hits55, hits56, hits57, hits58, hits59, hits60, hits61, hits62, hits63, hits64, hits65, hits66, hits67, hits68, List.append_assoc]

theorem allTargets (dest : Nat) : Decode.isValidJumpDest reference dest =
    Decode.isValidJumpDest code dest :=
  equal_all_targets StaticDomainFrontier64.completePath completePath equalHits dest

theorem allWindows : LocalDecode.checkMany reference code
    (StaticDomainFrontier64.pcs.filter (fun pc => decide (Exterior pc))) = true := by
  simp only [StaticDomainFrontier64.pcs, List.filter_append, LocalDecode.checkMany, List.all_append]
  have h00 := windows00
  have h01 := windows01
  have h02 := windows02
  have h03 := windows03
  have h04 := windows04
  have h05 := windows05
  have h06 := windows06
  have h07 := windows07
  have h08 := windows08
  have h09 := windows09
  have h10 := windows10
  have h11 := windows11
  have h12 := windows12
  have h13 := windows13
  have h14 := windows14
  have h15 := windows15
  have h16 := windows16
  have h17 := windows17
  have h18 := windows18
  have h19 := windows19
  have h20 := windows20
  have h21 := windows21
  have h22 := windows22
  have h23 := windows23
  have h24 := windows24
  have h25 := windows25
  have h26 := windows26
  have h27 := windows27
  have h28 := windows28
  have h29 := windows29
  have h30 := windows30
  have h31 := windows31
  have h32 := windows32
  have h33 := windows33
  have h34 := windows34
  have h35 := windows35
  have h36 := windows36
  have h37 := windows37
  have h38 := windows38
  have h39 := windows39
  have h40 := windows40
  have h41 := windows41
  have h42 := windows42
  have h43 := windows43
  have h44 := windows44
  have h45 := windows45
  have h46 := windows46
  have h47 := windows47
  have h48 := windows48
  have h49 := windows49
  have h50 := windows50
  have h51 := windows51
  have h52 := windows52
  have h53 := windows53
  have h54 := windows54
  have h55 := windows55
  have h56 := windows56
  have h57 := windows57
  have h58 := windows58
  have h59 := windows59
  have h60 := windows60
  have h61 := windows61
  have h62 := windows62
  have h63 := windows63
  have h64 := windows64
  have h65 := windows65
  have h66 := windows66
  have h67 := windows67
  have h68 := windows68
  simp only [LocalDecode.checkMany] at h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68
  simp only [h00, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68]

def sites : Sites code where
  code := ⟨by decide, by decide, by decide, by decide⟩
  windows := allWindows
  targets := allTargets

/-- Closed different-code refinement; no local machine-state premise remains. -/
def refinement : Challenge.Modexp.Submission.Isolation.ForwardRefinement reference code :=
  PointerSub32.refinement sites

example : code ≠ reference := by
  intro he
  have h := congrArg (fun b : ByteArray => b[2539]!) he
  change (0x61 : UInt8) = 0x80 at h
  exact (by decide : (0x61 : UInt8) ≠ 0x80) h

#print axioms refinement
end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
