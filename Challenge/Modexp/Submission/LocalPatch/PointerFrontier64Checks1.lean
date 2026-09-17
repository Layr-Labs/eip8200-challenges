import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Checks0

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk14 : List Nat := StaticDomainFrontier64.pcs14

theorem path14 : ScanPath code 1156 walk14 1226 := by decide

theorem hits14 : targets reference StaticDomainFrontier64.pcs14 = targets code walk14 := by decide

theorem windows14 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs14.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk15 : List Nat := StaticDomainFrontier64.pcs15

theorem path15 : ScanPath code 1226 walk15 1296 := by decide

theorem hits15 : targets reference StaticDomainFrontier64.pcs15 = targets code walk15 := by decide

theorem windows15 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs15.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk16 : List Nat := StaticDomainFrontier64.pcs16

theorem path16 : ScanPath code 1296 walk16 1366 := by decide

theorem hits16 : targets reference StaticDomainFrontier64.pcs16 = targets code walk16 := by decide

theorem windows16 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs16.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk17 : List Nat := StaticDomainFrontier64.pcs17

theorem path17 : ScanPath code 1366 walk17 1442 := by decide

theorem hits17 : targets reference StaticDomainFrontier64.pcs17 = targets code walk17 := by decide

theorem windows17 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs17.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk18 : List Nat := StaticDomainFrontier64.pcs18

theorem path18 : ScanPath code 1442 walk18 1512 := by decide

theorem hits18 : targets reference StaticDomainFrontier64.pcs18 = targets code walk18 := by decide

theorem windows18 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs18.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk19 : List Nat := StaticDomainFrontier64.pcs19

theorem path19 : ScanPath code 1512 walk19 1582 := by decide

theorem hits19 : targets reference StaticDomainFrontier64.pcs19 = targets code walk19 := by decide

theorem windows19 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs19.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk20 : List Nat := StaticDomainFrontier64.pcs20

theorem path20 : ScanPath code 1582 walk20 1654 := by decide

theorem hits20 : targets reference StaticDomainFrontier64.pcs20 = targets code walk20 := by decide

theorem windows20 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs20.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk21 : List Nat := StaticDomainFrontier64.pcs21

theorem path21 : ScanPath code 1654 walk21 1724 := by decide

theorem hits21 : targets reference StaticDomainFrontier64.pcs21 = targets code walk21 := by decide

theorem windows21 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs21.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk22 : List Nat := StaticDomainFrontier64.pcs22

theorem path22 : ScanPath code 1724 walk22 1796 := by decide

theorem hits22 : targets reference StaticDomainFrontier64.pcs22 = targets code walk22 := by decide

theorem windows22 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs22.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk23 : List Nat := StaticDomainFrontier64.pcs23

theorem path23 : ScanPath code 1796 walk23 1866 := by decide

theorem hits23 : targets reference StaticDomainFrontier64.pcs23 = targets code walk23 := by decide

theorem windows23 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs23.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk24 : List Nat := StaticDomainFrontier64.pcs24

theorem path24 : ScanPath code 1866 walk24 1943 := by decide

theorem hits24 : targets reference StaticDomainFrontier64.pcs24 = targets code walk24 := by decide

theorem windows24 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs24.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk25 : List Nat := StaticDomainFrontier64.pcs25

theorem path25 : ScanPath code 1943 walk25 2013 := by decide

theorem hits25 : targets reference StaticDomainFrontier64.pcs25 = targets code walk25 := by decide

theorem windows25 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs25.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk26 : List Nat := StaticDomainFrontier64.pcs26

theorem path26 : ScanPath code 2013 walk26 2085 := by decide

theorem hits26 : targets reference StaticDomainFrontier64.pcs26 = targets code walk26 := by decide

theorem windows26 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs26.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk27 : List Nat := StaticDomainFrontier64.pcs27

theorem path27 : ScanPath code 2085 walk27 2155 := by decide

theorem hits27 : targets reference StaticDomainFrontier64.pcs27 = targets code walk27 := by decide

theorem windows27 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs27.filter (fun pc => decide (Exterior pc))) = true := by decide

end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
