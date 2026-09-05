import Challenge.Ripemd160.Submission.H39Memo.DispatchState

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.DispatchTable

structure PatternSite where
  size : Nat
  entryPC : Nat
  entryIndex : Nat
  checkOffset : Option Nat
  outputPC : Nat
  outputIndex : Nat
  returnPC : Nat

def emptySite : PatternSite :=
  { size := 0
    entryPC := 3264
    entryIndex := 1158
    checkOffset := none
    outputPC := 3266
    outputIndex := 1160
    returnPC := 3292 }

def abcSite : PatternSite :=
  { size := 3
    entryPC := 3293
    entryIndex := 1166
    checkOffset := some 0
    outputPC := 3335
    outputIndex := 1174
    returnPC := 3361 }

def patternedSites : List PatternSite :=
  [ { size := 1, entryPC := 3362, entryIndex := 1180,
      checkOffset := some 0, outputPC := 3404, outputIndex := 1188,
      returnPC := 3430 }
  , { size := 31, entryPC := 3431, entryIndex := 1194,
      checkOffset := some 0, outputPC := 3473, outputIndex := 1202,
      returnPC := 3499 }
  , { size := 32, entryPC := 3500, entryIndex := 1208,
      checkOffset := none, outputPC := 3502, outputIndex := 1210,
      returnPC := 3528 }
  , { size := 55, entryPC := 3529, entryIndex := 1216,
      checkOffset := some 32, outputPC := 3572, outputIndex := 1224,
      returnPC := 3598 }
  , { size := 56, entryPC := 3599, entryIndex := 1230,
      checkOffset := some 32, outputPC := 3642, outputIndex := 1238,
      returnPC := 3668 }
  , { size := 63, entryPC := 3669, entryIndex := 1244,
      checkOffset := some 32, outputPC := 3712, outputIndex := 1252,
      returnPC := 3738 }
  , { size := 64, entryPC := 3739, entryIndex := 1258,
      checkOffset := none, outputPC := 3741, outputIndex := 1260,
      returnPC := 3767 }
  , { size := 65, entryPC := 3768, entryIndex := 1266,
      checkOffset := some 64, outputPC := 3811, outputIndex := 1274,
      returnPC := 3837 }
  , { size := 119, entryPC := 3838, entryIndex := 1280,
      checkOffset := some 96, outputPC := 3881, outputIndex := 1288,
      returnPC := 3907 }
  , { size := 120, entryPC := 3908, entryIndex := 1294,
      checkOffset := some 96, outputPC := 3951, outputIndex := 1302,
      returnPC := 3977 }
  , { size := 128, entryPC := 3978, entryIndex := 1308,
      checkOffset := none, outputPC := 3980, outputIndex := 1310,
      returnPC := 4006 }
  , { size := 256, entryPC := 4007, entryIndex := 1316,
      checkOffset := none, outputPC := 4009, outputIndex := 1318,
      returnPC := 4035 }
  , { size := 376, entryPC := 4036, entryIndex := 1324,
      checkOffset := some 352, outputPC := 4080, outputIndex := 1332,
      returnPC := 4106 }
  , { size := 1000, entryPC := 4107, entryIndex := 1338,
      checkOffset := some 992, outputPC := 4151, outputIndex := 1346,
      returnPC := 4177 } ]

def siteForSize (size : Nat) : Option PatternSite :=
  patternedSites.find? (fun site => site.size = size)

@[simp] theorem patternedSites_sizes :
    patternedSites.map PatternSite.size =
      [1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 256, 376, 1000] := by
  rfl

@[simp] theorem siteForSize_1 : siteForSize 1 = some
    { size := 1, entryPC := 3362, entryIndex := 1180,
      checkOffset := some 0, outputPC := 3404, outputIndex := 1188,
      returnPC := 3430 } := by
  rfl

@[simp] theorem siteForSize_1000 :
    (siteForSize 1000).map PatternSite.entryPC = some 4107 := by
  rfl

end Challenge.Ripemd160.Submission.H39Memo.DispatchTable
