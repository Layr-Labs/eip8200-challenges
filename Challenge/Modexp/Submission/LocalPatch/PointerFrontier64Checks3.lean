import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Checks2

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk42 : List Nat := StaticDomainFrontier64.pcs42

theorem path42 : ScanPath code 3319 walk42 3414 := by decide

theorem hits42 : targets reference StaticDomainFrontier64.pcs42 = targets code walk42 := by decide

theorem windows42 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs42.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk43 : List Nat := StaticDomainFrontier64.pcs43

theorem path43 : ScanPath code 3414 walk43 3498 := by decide

theorem hits43 : targets reference StaticDomainFrontier64.pcs43 = targets code walk43 := by decide

theorem windows43 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs43.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk44 : List Nat := StaticDomainFrontier64.pcs44

theorem path44 : ScanPath code 3498 walk44 3574 := by decide

theorem hits44 : targets reference StaticDomainFrontier64.pcs44 = targets code walk44 := by decide

theorem windows44 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs44.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk45 : List Nat := StaticDomainFrontier64.pcs45

theorem path45 : ScanPath code 3574 walk45 3650 := by decide

theorem hits45 : targets reference StaticDomainFrontier64.pcs45 = targets code walk45 := by decide

theorem windows45 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs45.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk46 : List Nat := StaticDomainFrontier64.pcs46

theorem path46 : ScanPath code 3650 walk46 3726 := by decide

theorem hits46 : targets reference StaticDomainFrontier64.pcs46 = targets code walk46 := by decide

theorem windows46 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs46.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk47 : List Nat := StaticDomainFrontier64.pcs47

theorem path47 : ScanPath code 3726 walk47 3812 := by decide

theorem hits47 : targets reference StaticDomainFrontier64.pcs47 = targets code walk47 := by decide

theorem windows47 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs47.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk48 : List Nat := StaticDomainFrontier64.pcs48

theorem path48 : ScanPath code 3812 walk48 3886 := by decide

theorem hits48 : targets reference StaticDomainFrontier64.pcs48 = targets code walk48 := by decide

theorem windows48 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs48.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk49 : List Nat := StaticDomainFrontier64.pcs49

theorem path49 : ScanPath code 3886 walk49 3961 := by decide

theorem hits49 : targets reference StaticDomainFrontier64.pcs49 = targets code walk49 := by decide

theorem windows49 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs49.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk50 : List Nat := StaticDomainFrontier64.pcs50

theorem path50 : ScanPath code 3961 walk50 4035 := by decide

theorem hits50 : targets reference StaticDomainFrontier64.pcs50 = targets code walk50 := by decide

theorem windows50 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs50.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk51 : List Nat := StaticDomainFrontier64.pcs51

theorem path51 : ScanPath code 4035 walk51 4126 := by decide

theorem hits51 : targets reference StaticDomainFrontier64.pcs51 = targets code walk51 := by decide

theorem windows51 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs51.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk52 : List Nat := StaticDomainFrontier64.pcs52

theorem path52 : ScanPath code 4126 walk52 4214 := by decide

theorem hits52 : targets reference StaticDomainFrontier64.pcs52 = targets code walk52 := by decide

theorem windows52 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs52.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk53 : List Nat := StaticDomainFrontier64.pcs53

theorem path53 : ScanPath code 4214 walk53 4305 := by decide

theorem hits53 : targets reference StaticDomainFrontier64.pcs53 = targets code walk53 := by decide

theorem windows53 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs53.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk54 : List Nat := StaticDomainFrontier64.pcs54

theorem path54 : ScanPath code 4305 walk54 4391 := by decide

theorem hits54 : targets reference StaticDomainFrontier64.pcs54 = targets code walk54 := by decide

theorem windows54 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs54.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk55 : List Nat := StaticDomainFrontier64.pcs55

theorem path55 : ScanPath code 4391 walk55 4485 := by decide

theorem hits55 : targets reference StaticDomainFrontier64.pcs55 = targets code walk55 := by decide

theorem windows55 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs55.filter (fun pc => decide (Exterior pc))) = true := by decide

end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
