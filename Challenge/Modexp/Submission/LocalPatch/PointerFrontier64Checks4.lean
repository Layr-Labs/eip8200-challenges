import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Checks3

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk56 : List Nat := StaticDomainFrontier64.pcs56

theorem path56 : ScanPath code 4485 walk56 4565 := by decide

theorem hits56 : targets reference StaticDomainFrontier64.pcs56 = targets code walk56 := by decide

theorem windows56 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs56.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk57 : List Nat := StaticDomainFrontier64.pcs57

theorem path57 : ScanPath code 4565 walk57 4639 := by decide

theorem hits57 : targets reference StaticDomainFrontier64.pcs57 = targets code walk57 := by decide

theorem windows57 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs57.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk58 : List Nat := StaticDomainFrontier64.pcs58

theorem path58 : ScanPath code 4639 walk58 4707 := by decide

theorem hits58 : targets reference StaticDomainFrontier64.pcs58 = targets code walk58 := by decide

theorem windows58 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs58.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk59 : List Nat := StaticDomainFrontier64.pcs59

theorem path59 : ScanPath code 4707 walk59 4781 := by decide

theorem hits59 : targets reference StaticDomainFrontier64.pcs59 = targets code walk59 := by decide

theorem windows59 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs59.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk60 : List Nat := StaticDomainFrontier64.pcs60

theorem path60 : ScanPath code 4781 walk60 4853 := by decide

theorem hits60 : targets reference StaticDomainFrontier64.pcs60 = targets code walk60 := by decide

theorem windows60 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs60.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk61 : List Nat := StaticDomainFrontier64.pcs61

theorem path61 : ScanPath code 4853 walk61 4919 := by decide

theorem hits61 : targets reference StaticDomainFrontier64.pcs61 = targets code walk61 := by decide

theorem windows61 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs61.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk62 : List Nat := StaticDomainFrontier64.pcs62

theorem path62 : ScanPath code 4919 walk62 5005 := by decide

theorem hits62 : targets reference StaticDomainFrontier64.pcs62 = targets code walk62 := by decide

theorem windows62 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs62.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk63 : List Nat := StaticDomainFrontier64.pcs63

theorem path63 : ScanPath code 5005 walk63 5077 := by decide

theorem hits63 : targets reference StaticDomainFrontier64.pcs63 = targets code walk63 := by decide

theorem windows63 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs63.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk64 : List Nat := StaticDomainFrontier64.pcs64

theorem path64 : ScanPath code 5077 walk64 5153 := by decide

theorem hits64 : targets reference StaticDomainFrontier64.pcs64 = targets code walk64 := by decide

theorem windows64 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs64.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk65 : List Nat := StaticDomainFrontier64.pcs65

theorem path65 : ScanPath code 5153 walk65 5227 := by decide

theorem hits65 : targets reference StaticDomainFrontier64.pcs65 = targets code walk65 := by decide

theorem windows65 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs65.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk66 : List Nat := StaticDomainFrontier64.pcs66

theorem path66 : ScanPath code 5227 walk66 5311 := by decide

theorem hits66 : targets reference StaticDomainFrontier64.pcs66 = targets code walk66 := by decide

theorem windows66 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs66.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk67 : List Nat := StaticDomainFrontier64.pcs67

theorem path67 : ScanPath code 5311 walk67 5389 := by decide

theorem hits67 : targets reference StaticDomainFrontier64.pcs67 = targets code walk67 := by decide

theorem windows67 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs67.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk68 : List Nat := StaticDomainFrontier64.pcs68

theorem path68 : ScanPath code 5389 walk68 5439 := by decide

theorem hits68 : targets reference StaticDomainFrontier64.pcs68 = targets code walk68 := by decide

theorem windows68 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs68.filter (fun pc => decide (Exterior pc))) = true := by decide

end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
