import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Instruction-offset table for the `addMaskedMod` region

`ProgramArtifact.instructionPC index` is the length of the assembled prefix, so
proving one such fact by `rfl` costs a whole prefix assembly — about 0.23 s at
these indices.  Stating a table of them per index is therefore *quadratic* and
dominates the cost of the block layer that consumes it.

Instead this module assembles exactly **two** prefixes by `rfl` (the entries of
the in-place trampoline and of the appended body) and derives every other
offset with a single `pcSuccOp` / `pcSuccPush` step.  Each step needs only the
instruction at the previous index, which the block layer looks up anyway.

Kept in its own module so the table compiles once into an `olean` and the
block-proof edit loop never pays for it again.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- One instruction later is one opcode byte later. -/
theorem pcSuccOp {index : Nat} {op : EvmSemantics.Operation}
    (hget : Artifact.submissionInstructions[index]? = some (.op op)) :
    Artifact.submissionArtifact.instructionPC (index + 1) =
      Artifact.submissionArtifact.instructionPC index + 1 := by
  show (assembleBytes (Artifact.submissionInstructions.take (index + 1))).length =
    (assembleBytes (Artifact.submissionInstructions.take index)).length + 1
  rw [List.take_add_one, hget]
  simp [assembleBytes_append]

/-- One `PUSHk` later is `1 + k` bytes later. -/
theorem pcSuccPush {index : Nat} {w : Fin 33} {v : UInt256}
    (hget : Artifact.submissionInstructions[index]? = some (.push w v)) :
    Artifact.submissionArtifact.instructionPC (index + 1) =
      Artifact.submissionArtifact.instructionPC index + (1 + w.val) := by
  show (assembleBytes (Artifact.submissionInstructions.take (index + 1))).length =
    (assembleBytes (Artifact.submissionInstructions.take index)).length + (1 + w.val)
  rw [List.take_add_one, hget]
  simp [assembleBytes_append]

/-! ### The in-place trampoline `JUMPDEST; PUSH2 0x074b; JUMP` -/

@[simp] theorem ammPC83 :
    Artifact.submissionArtifact.instructionPC 83 = 104 := by rfl
@[simp] theorem ammPC84 :
    Artifact.submissionArtifact.instructionPC 84 = 105 := by
  have h := pcSuccOp (index := 83) (by rfl)
  rw [ammPC83] at h; simpa using h
@[simp] theorem ammPC85 :
    Artifact.submissionArtifact.instructionPC 85 = 108 := by
  have h := pcSuccPush (index := 84) (by rfl)
  rw [ammPC84] at h; simpa using h

/-! ### The appended body at `0x074b` -/

@[simp] theorem ammPC1356 :
    Artifact.submissionArtifact.instructionPC 1356 = 1867 := by rfl
@[simp] theorem ammPC1357 :
    Artifact.submissionArtifact.instructionPC 1357 = 1868 := by
  have h := pcSuccOp (index := 1356) (by rfl)
  rw [ammPC1356] at h; simpa using h
@[simp] theorem ammPC1358 :
    Artifact.submissionArtifact.instructionPC 1358 = 1869 := by
  have h := pcSuccOp (index := 1357) (by rfl)
  rw [ammPC1357] at h; simpa using h
@[simp] theorem ammPC1359 :
    Artifact.submissionArtifact.instructionPC 1359 = 1870 := by
  have h := pcSuccPush (index := 1358) (by rfl)
  rw [ammPC1358] at h; simpa using h
@[simp] theorem ammPC1360 :
    Artifact.submissionArtifact.instructionPC 1360 = 1871 := by
  have h := pcSuccOp (index := 1359) (by rfl)
  rw [ammPC1359] at h; simpa using h
@[simp] theorem ammPC1361 :
    Artifact.submissionArtifact.instructionPC 1361 = 1872 := by
  have h := pcSuccOp (index := 1360) (by rfl)
  rw [ammPC1360] at h; simpa using h
@[simp] theorem ammPC1362 :
    Artifact.submissionArtifact.instructionPC 1362 = 1873 := by
  have h := pcSuccOp (index := 1361) (by rfl)
  rw [ammPC1361] at h; simpa using h
@[simp] theorem ammPC1363 :
    Artifact.submissionArtifact.instructionPC 1363 = 1874 := by
  have h := pcSuccOp (index := 1362) (by rfl)
  rw [ammPC1362] at h; simpa using h
@[simp] theorem ammPC1364 :
    Artifact.submissionArtifact.instructionPC 1364 = 1875 := by
  have h := pcSuccOp (index := 1363) (by rfl)
  rw [ammPC1363] at h; simpa using h
@[simp] theorem ammPC1365 :
    Artifact.submissionArtifact.instructionPC 1365 = 1876 := by
  have h := pcSuccOp (index := 1364) (by rfl)
  rw [ammPC1364] at h; simpa using h
@[simp] theorem ammPC1366 :
    Artifact.submissionArtifact.instructionPC 1366 = 1877 := by
  have h := pcSuccOp (index := 1365) (by rfl)
  rw [ammPC1365] at h; simpa using h
@[simp] theorem ammPC1367 :
    Artifact.submissionArtifact.instructionPC 1367 = 1878 := by
  have h := pcSuccOp (index := 1366) (by rfl)
  rw [ammPC1366] at h; simpa using h
@[simp] theorem ammPC1368 :
    Artifact.submissionArtifact.instructionPC 1368 = 1880 := by
  have h := pcSuccPush (index := 1367) (by rfl)
  rw [ammPC1367] at h; simpa using h
@[simp] theorem ammPC1369 :
    Artifact.submissionArtifact.instructionPC 1369 = 1881 := by
  have h := pcSuccOp (index := 1368) (by rfl)
  rw [ammPC1368] at h; simpa using h
@[simp] theorem ammPC1370 :
    Artifact.submissionArtifact.instructionPC 1370 = 1882 := by
  have h := pcSuccOp (index := 1369) (by rfl)
  rw [ammPC1369] at h; simpa using h
@[simp] theorem ammPC1371 :
    Artifact.submissionArtifact.instructionPC 1371 = 1883 := by
  have h := pcSuccOp (index := 1370) (by rfl)
  rw [ammPC1370] at h; simpa using h
@[simp] theorem ammPC1372 :
    Artifact.submissionArtifact.instructionPC 1372 = 1884 := by
  have h := pcSuccPush (index := 1371) (by rfl)
  rw [ammPC1371] at h; simpa using h
@[simp] theorem ammPC1373 :
    Artifact.submissionArtifact.instructionPC 1373 = 1885 := by
  have h := pcSuccPush (index := 1372) (by rfl)
  rw [ammPC1372] at h; simpa using h
@[simp] theorem ammPC1374 :
    Artifact.submissionArtifact.instructionPC 1374 = 1886 := by
  have h := pcSuccOp (index := 1373) (by rfl)
  rw [ammPC1373] at h; simpa using h
@[simp] theorem ammPC1375 :
    Artifact.submissionArtifact.instructionPC 1375 = 1887 := by
  have h := pcSuccOp (index := 1374) (by rfl)
  rw [ammPC1374] at h; simpa using h
@[simp] theorem ammPC1376 :
    Artifact.submissionArtifact.instructionPC 1376 = 1888 := by
  have h := pcSuccOp (index := 1375) (by rfl)
  rw [ammPC1375] at h; simpa using h
@[simp] theorem ammPC1377 :
    Artifact.submissionArtifact.instructionPC 1377 = 1889 := by
  have h := pcSuccOp (index := 1376) (by rfl)
  rw [ammPC1376] at h; simpa using h
@[simp] theorem ammPC1378 :
    Artifact.submissionArtifact.instructionPC 1378 = 1890 := by
  have h := pcSuccOp (index := 1377) (by rfl)
  rw [ammPC1377] at h; simpa using h
@[simp] theorem ammPC1379 :
    Artifact.submissionArtifact.instructionPC 1379 = 1893 := by
  have h := pcSuccPush (index := 1378) (by rfl)
  rw [ammPC1378] at h; simpa using h
@[simp] theorem ammPC1380 :
    Artifact.submissionArtifact.instructionPC 1380 = 1894 := by
  have h := pcSuccOp (index := 1379) (by rfl)
  rw [ammPC1379] at h; simpa using h
@[simp] theorem ammPC1381 :
    Artifact.submissionArtifact.instructionPC 1381 = 1895 := by
  have h := pcSuccOp (index := 1380) (by rfl)
  rw [ammPC1380] at h; simpa using h
@[simp] theorem ammPC1382 :
    Artifact.submissionArtifact.instructionPC 1382 = 1896 := by
  have h := pcSuccOp (index := 1381) (by rfl)
  rw [ammPC1381] at h; simpa using h
@[simp] theorem ammPC1383 :
    Artifact.submissionArtifact.instructionPC 1383 = 1897 := by
  have h := pcSuccOp (index := 1382) (by rfl)
  rw [ammPC1382] at h; simpa using h
@[simp] theorem ammPC1384 :
    Artifact.submissionArtifact.instructionPC 1384 = 1898 := by
  have h := pcSuccOp (index := 1383) (by rfl)
  rw [ammPC1383] at h; simpa using h
@[simp] theorem ammPC1385 :
    Artifact.submissionArtifact.instructionPC 1385 = 1899 := by
  have h := pcSuccOp (index := 1384) (by rfl)
  rw [ammPC1384] at h; simpa using h
@[simp] theorem ammPC1386 :
    Artifact.submissionArtifact.instructionPC 1386 = 1900 := by
  have h := pcSuccOp (index := 1385) (by rfl)
  rw [ammPC1385] at h; simpa using h
@[simp] theorem ammPC1387 :
    Artifact.submissionArtifact.instructionPC 1387 = 1901 := by
  have h := pcSuccOp (index := 1386) (by rfl)
  rw [ammPC1386] at h; simpa using h
@[simp] theorem ammPC1388 :
    Artifact.submissionArtifact.instructionPC 1388 = 1902 := by
  have h := pcSuccOp (index := 1387) (by rfl)
  rw [ammPC1387] at h; simpa using h
@[simp] theorem ammPC1389 :
    Artifact.submissionArtifact.instructionPC 1389 = 1903 := by
  have h := pcSuccOp (index := 1388) (by rfl)
  rw [ammPC1388] at h; simpa using h
@[simp] theorem ammPC1390 :
    Artifact.submissionArtifact.instructionPC 1390 = 1904 := by
  have h := pcSuccOp (index := 1389) (by rfl)
  rw [ammPC1389] at h; simpa using h
@[simp] theorem ammPC1391 :
    Artifact.submissionArtifact.instructionPC 1391 = 1905 := by
  have h := pcSuccOp (index := 1390) (by rfl)
  rw [ammPC1390] at h; simpa using h
@[simp] theorem ammPC1392 :
    Artifact.submissionArtifact.instructionPC 1392 = 1906 := by
  have h := pcSuccOp (index := 1391) (by rfl)
  rw [ammPC1391] at h; simpa using h
@[simp] theorem ammPC1393 :
    Artifact.submissionArtifact.instructionPC 1393 = 1907 := by
  have h := pcSuccOp (index := 1392) (by rfl)
  rw [ammPC1392] at h; simpa using h
@[simp] theorem ammPC1394 :
    Artifact.submissionArtifact.instructionPC 1394 = 1908 := by
  have h := pcSuccOp (index := 1393) (by rfl)
  rw [ammPC1393] at h; simpa using h
@[simp] theorem ammPC1395 :
    Artifact.submissionArtifact.instructionPC 1395 = 1909 := by
  have h := pcSuccOp (index := 1394) (by rfl)
  rw [ammPC1394] at h; simpa using h
@[simp] theorem ammPC1396 :
    Artifact.submissionArtifact.instructionPC 1396 = 1910 := by
  have h := pcSuccOp (index := 1395) (by rfl)
  rw [ammPC1395] at h; simpa using h
@[simp] theorem ammPC1397 :
    Artifact.submissionArtifact.instructionPC 1397 = 1911 := by
  have h := pcSuccOp (index := 1396) (by rfl)
  rw [ammPC1396] at h; simpa using h
@[simp] theorem ammPC1398 :
    Artifact.submissionArtifact.instructionPC 1398 = 1912 := by
  have h := pcSuccOp (index := 1397) (by rfl)
  rw [ammPC1397] at h; simpa using h
@[simp] theorem ammPC1399 :
    Artifact.submissionArtifact.instructionPC 1399 = 1913 := by
  have h := pcSuccOp (index := 1398) (by rfl)
  rw [ammPC1398] at h; simpa using h
@[simp] theorem ammPC1400 :
    Artifact.submissionArtifact.instructionPC 1400 = 1914 := by
  have h := pcSuccOp (index := 1399) (by rfl)
  rw [ammPC1399] at h; simpa using h
@[simp] theorem ammPC1401 :
    Artifact.submissionArtifact.instructionPC 1401 = 1915 := by
  have h := pcSuccOp (index := 1400) (by rfl)
  rw [ammPC1400] at h; simpa using h
@[simp] theorem ammPC1402 :
    Artifact.submissionArtifact.instructionPC 1402 = 1916 := by
  have h := pcSuccOp (index := 1401) (by rfl)
  rw [ammPC1401] at h; simpa using h
@[simp] theorem ammPC1403 :
    Artifact.submissionArtifact.instructionPC 1403 = 1917 := by
  have h := pcSuccOp (index := 1402) (by rfl)
  rw [ammPC1402] at h; simpa using h
@[simp] theorem ammPC1404 :
    Artifact.submissionArtifact.instructionPC 1404 = 1918 := by
  have h := pcSuccOp (index := 1403) (by rfl)
  rw [ammPC1403] at h; simpa using h
@[simp] theorem ammPC1405 :
    Artifact.submissionArtifact.instructionPC 1405 = 1919 := by
  have h := pcSuccOp (index := 1404) (by rfl)
  rw [ammPC1404] at h; simpa using h
@[simp] theorem ammPC1406 :
    Artifact.submissionArtifact.instructionPC 1406 = 1920 := by
  have h := pcSuccOp (index := 1405) (by rfl)
  rw [ammPC1405] at h; simpa using h
@[simp] theorem ammPC1407 :
    Artifact.submissionArtifact.instructionPC 1407 = 1921 := by
  have h := pcSuccOp (index := 1406) (by rfl)
  rw [ammPC1406] at h; simpa using h
@[simp] theorem ammPC1408 :
    Artifact.submissionArtifact.instructionPC 1408 = 1922 := by
  have h := pcSuccOp (index := 1407) (by rfl)
  rw [ammPC1407] at h; simpa using h
@[simp] theorem ammPC1409 :
    Artifact.submissionArtifact.instructionPC 1409 = 1923 := by
  have h := pcSuccOp (index := 1408) (by rfl)
  rw [ammPC1408] at h; simpa using h
@[simp] theorem ammPC1410 :
    Artifact.submissionArtifact.instructionPC 1410 = 1924 := by
  have h := pcSuccOp (index := 1409) (by rfl)
  rw [ammPC1409] at h; simpa using h
@[simp] theorem ammPC1411 :
    Artifact.submissionArtifact.instructionPC 1411 = 1925 := by
  have h := pcSuccOp (index := 1410) (by rfl)
  rw [ammPC1410] at h; simpa using h
@[simp] theorem ammPC1412 :
    Artifact.submissionArtifact.instructionPC 1412 = 1926 := by
  have h := pcSuccOp (index := 1411) (by rfl)
  rw [ammPC1411] at h; simpa using h
@[simp] theorem ammPC1413 :
    Artifact.submissionArtifact.instructionPC 1413 = 1927 := by
  have h := pcSuccOp (index := 1412) (by rfl)
  rw [ammPC1412] at h; simpa using h
@[simp] theorem ammPC1414 :
    Artifact.submissionArtifact.instructionPC 1414 = 1928 := by
  have h := pcSuccOp (index := 1413) (by rfl)
  rw [ammPC1413] at h; simpa using h
@[simp] theorem ammPC1415 :
    Artifact.submissionArtifact.instructionPC 1415 = 1929 := by
  have h := pcSuccOp (index := 1414) (by rfl)
  rw [ammPC1414] at h; simpa using h
@[simp] theorem ammPC1416 :
    Artifact.submissionArtifact.instructionPC 1416 = 1930 := by
  have h := pcSuccOp (index := 1415) (by rfl)
  rw [ammPC1415] at h; simpa using h
@[simp] theorem ammPC1417 :
    Artifact.submissionArtifact.instructionPC 1417 = 1931 := by
  have h := pcSuccOp (index := 1416) (by rfl)
  rw [ammPC1416] at h; simpa using h
@[simp] theorem ammPC1418 :
    Artifact.submissionArtifact.instructionPC 1418 = 1932 := by
  have h := pcSuccOp (index := 1417) (by rfl)
  rw [ammPC1417] at h; simpa using h
@[simp] theorem ammPC1419 :
    Artifact.submissionArtifact.instructionPC 1419 = 1933 := by
  have h := pcSuccOp (index := 1418) (by rfl)
  rw [ammPC1418] at h; simpa using h
@[simp] theorem ammPC1420 :
    Artifact.submissionArtifact.instructionPC 1420 = 1934 := by
  have h := pcSuccOp (index := 1419) (by rfl)
  rw [ammPC1419] at h; simpa using h
@[simp] theorem ammPC1421 :
    Artifact.submissionArtifact.instructionPC 1421 = 1935 := by
  have h := pcSuccOp (index := 1420) (by rfl)
  rw [ammPC1420] at h; simpa using h
@[simp] theorem ammPC1422 :
    Artifact.submissionArtifact.instructionPC 1422 = 1936 := by
  have h := pcSuccOp (index := 1421) (by rfl)
  rw [ammPC1421] at h; simpa using h
@[simp] theorem ammPC1423 :
    Artifact.submissionArtifact.instructionPC 1423 = 1937 := by
  have h := pcSuccOp (index := 1422) (by rfl)
  rw [ammPC1422] at h; simpa using h
@[simp] theorem ammPC1424 :
    Artifact.submissionArtifact.instructionPC 1424 = 1939 := by
  have h := pcSuccPush (index := 1423) (by rfl)
  rw [ammPC1423] at h; simpa using h
@[simp] theorem ammPC1425 :
    Artifact.submissionArtifact.instructionPC 1425 = 1940 := by
  have h := pcSuccOp (index := 1424) (by rfl)
  rw [ammPC1424] at h; simpa using h
@[simp] theorem ammPC1426 :
    Artifact.submissionArtifact.instructionPC 1426 = 1941 := by
  have h := pcSuccOp (index := 1425) (by rfl)
  rw [ammPC1425] at h; simpa using h
@[simp] theorem ammPC1427 :
    Artifact.submissionArtifact.instructionPC 1427 = 1942 := by
  have h := pcSuccOp (index := 1426) (by rfl)
  rw [ammPC1426] at h; simpa using h
@[simp] theorem ammPC1428 :
    Artifact.submissionArtifact.instructionPC 1428 = 1943 := by
  have h := pcSuccOp (index := 1427) (by rfl)
  rw [ammPC1427] at h; simpa using h
@[simp] theorem ammPC1429 :
    Artifact.submissionArtifact.instructionPC 1429 = 1946 := by
  have h := pcSuccPush (index := 1428) (by rfl)
  rw [ammPC1428] at h; simpa using h
@[simp] theorem ammPC1430 :
    Artifact.submissionArtifact.instructionPC 1430 = 1947 := by
  have h := pcSuccOp (index := 1429) (by rfl)
  rw [ammPC1429] at h; simpa using h
@[simp] theorem ammPC1431 :
    Artifact.submissionArtifact.instructionPC 1431 = 1948 := by
  have h := pcSuccOp (index := 1430) (by rfl)
  rw [ammPC1430] at h; simpa using h
@[simp] theorem ammPC1432 :
    Artifact.submissionArtifact.instructionPC 1432 = 1949 := by
  have h := pcSuccOp (index := 1431) (by rfl)
  rw [ammPC1431] at h; simpa using h
@[simp] theorem ammPC1433 :
    Artifact.submissionArtifact.instructionPC 1433 = 1950 := by
  have h := pcSuccOp (index := 1432) (by rfl)
  rw [ammPC1432] at h; simpa using h
@[simp] theorem ammPC1434 :
    Artifact.submissionArtifact.instructionPC 1434 = 1951 := by
  have h := pcSuccOp (index := 1433) (by rfl)
  rw [ammPC1433] at h; simpa using h
@[simp] theorem ammPC1435 :
    Artifact.submissionArtifact.instructionPC 1435 = 1952 := by
  have h := pcSuccOp (index := 1434) (by rfl)
  rw [ammPC1434] at h; simpa using h
@[simp] theorem ammPC1436 :
    Artifact.submissionArtifact.instructionPC 1436 = 1953 := by
  have h := pcSuccOp (index := 1435) (by rfl)
  rw [ammPC1435] at h; simpa using h
@[simp] theorem ammPC1437 :
    Artifact.submissionArtifact.instructionPC 1437 = 1956 := by
  have h := pcSuccPush (index := 1436) (by rfl)
  rw [ammPC1436] at h; simpa using h
@[simp] theorem ammPC1438 :
    Artifact.submissionArtifact.instructionPC 1438 = 1957 := by
  have h := pcSuccOp (index := 1437) (by rfl)
  rw [ammPC1437] at h; simpa using h
@[simp] theorem ammPC1439 :
    Artifact.submissionArtifact.instructionPC 1439 = 1958 := by
  have h := pcSuccOp (index := 1438) (by rfl)
  rw [ammPC1438] at h; simpa using h
@[simp] theorem ammPC1440 :
    Artifact.submissionArtifact.instructionPC 1440 = 1959 := by
  have h := pcSuccOp (index := 1439) (by rfl)
  rw [ammPC1439] at h; simpa using h
@[simp] theorem ammPC1441 :
    Artifact.submissionArtifact.instructionPC 1441 = 1960 := by
  have h := pcSuccOp (index := 1440) (by rfl)
  rw [ammPC1440] at h; simpa using h
@[simp] theorem ammPC1442 :
    Artifact.submissionArtifact.instructionPC 1442 = 1961 := by
  have h := pcSuccPush (index := 1441) (by rfl)
  rw [ammPC1441] at h; simpa using h
@[simp] theorem ammPC1443 :
    Artifact.submissionArtifact.instructionPC 1443 = 1962 := by
  have h := pcSuccOp (index := 1442) (by rfl)
  rw [ammPC1442] at h; simpa using h
@[simp] theorem ammPC1444 :
    Artifact.submissionArtifact.instructionPC 1444 = 1963 := by
  have h := pcSuccOp (index := 1443) (by rfl)
  rw [ammPC1443] at h; simpa using h
@[simp] theorem ammPC1445 :
    Artifact.submissionArtifact.instructionPC 1445 = 1964 := by
  have h := pcSuccOp (index := 1444) (by rfl)
  rw [ammPC1444] at h; simpa using h
@[simp] theorem ammPC1446 :
    Artifact.submissionArtifact.instructionPC 1446 = 1965 := by
  have h := pcSuccOp (index := 1445) (by rfl)
  rw [ammPC1445] at h; simpa using h
@[simp] theorem ammPC1447 :
    Artifact.submissionArtifact.instructionPC 1447 = 1966 := by
  have h := pcSuccOp (index := 1446) (by rfl)
  rw [ammPC1446] at h; simpa using h
@[simp] theorem ammPC1448 :
    Artifact.submissionArtifact.instructionPC 1448 = 1967 := by
  have h := pcSuccOp (index := 1447) (by rfl)
  rw [ammPC1447] at h; simpa using h
@[simp] theorem ammPC1449 :
    Artifact.submissionArtifact.instructionPC 1449 = 1970 := by
  have h := pcSuccPush (index := 1448) (by rfl)
  rw [ammPC1448] at h; simpa using h
@[simp] theorem ammPC1450 :
    Artifact.submissionArtifact.instructionPC 1450 = 1971 := by
  have h := pcSuccOp (index := 1449) (by rfl)
  rw [ammPC1449] at h; simpa using h
@[simp] theorem ammPC1451 :
    Artifact.submissionArtifact.instructionPC 1451 = 1972 := by
  have h := pcSuccOp (index := 1450) (by rfl)
  rw [ammPC1450] at h; simpa using h
@[simp] theorem ammPC1452 :
    Artifact.submissionArtifact.instructionPC 1452 = 1973 := by
  have h := pcSuccOp (index := 1451) (by rfl)
  rw [ammPC1451] at h; simpa using h
@[simp] theorem ammPC1453 :
    Artifact.submissionArtifact.instructionPC 1453 = 1974 := by
  have h := pcSuccOp (index := 1452) (by rfl)
  rw [ammPC1452] at h; simpa using h
@[simp] theorem ammPC1454 :
    Artifact.submissionArtifact.instructionPC 1454 = 1975 := by
  have h := pcSuccOp (index := 1453) (by rfl)
  rw [ammPC1453] at h; simpa using h
@[simp] theorem ammPC1455 :
    Artifact.submissionArtifact.instructionPC 1455 = 1976 := by
  have h := pcSuccOp (index := 1454) (by rfl)
  rw [ammPC1454] at h; simpa using h
@[simp] theorem ammPC1456 :
    Artifact.submissionArtifact.instructionPC 1456 = 1977 := by
  have h := pcSuccOp (index := 1455) (by rfl)
  rw [ammPC1455] at h; simpa using h
@[simp] theorem ammPC1457 :
    Artifact.submissionArtifact.instructionPC 1457 = 1978 := by
  have h := pcSuccOp (index := 1456) (by rfl)
  rw [ammPC1456] at h; simpa using h
@[simp] theorem ammPC1458 :
    Artifact.submissionArtifact.instructionPC 1458 = 1979 := by
  have h := pcSuccOp (index := 1457) (by rfl)
  rw [ammPC1457] at h; simpa using h
@[simp] theorem ammPC1459 :
    Artifact.submissionArtifact.instructionPC 1459 = 1980 := by
  have h := pcSuccOp (index := 1458) (by rfl)
  rw [ammPC1458] at h; simpa using h
@[simp] theorem ammPC1460 :
    Artifact.submissionArtifact.instructionPC 1460 = 1981 := by
  have h := pcSuccOp (index := 1459) (by rfl)
  rw [ammPC1459] at h; simpa using h
@[simp] theorem ammPC1461 :
    Artifact.submissionArtifact.instructionPC 1461 = 1982 := by
  have h := pcSuccOp (index := 1460) (by rfl)
  rw [ammPC1460] at h; simpa using h
@[simp] theorem ammPC1462 :
    Artifact.submissionArtifact.instructionPC 1462 = 1983 := by
  have h := pcSuccOp (index := 1461) (by rfl)
  rw [ammPC1461] at h; simpa using h
@[simp] theorem ammPC1463 :
    Artifact.submissionArtifact.instructionPC 1463 = 1984 := by
  have h := pcSuccOp (index := 1462) (by rfl)
  rw [ammPC1462] at h; simpa using h
@[simp] theorem ammPC1464 :
    Artifact.submissionArtifact.instructionPC 1464 = 1985 := by
  have h := pcSuccOp (index := 1463) (by rfl)
  rw [ammPC1463] at h; simpa using h
@[simp] theorem ammPC1465 :
    Artifact.submissionArtifact.instructionPC 1465 = 1986 := by
  have h := pcSuccOp (index := 1464) (by rfl)
  rw [ammPC1464] at h; simpa using h
@[simp] theorem ammPC1466 :
    Artifact.submissionArtifact.instructionPC 1466 = 1987 := by
  have h := pcSuccOp (index := 1465) (by rfl)
  rw [ammPC1465] at h; simpa using h
@[simp] theorem ammPC1467 :
    Artifact.submissionArtifact.instructionPC 1467 = 1988 := by
  have h := pcSuccOp (index := 1466) (by rfl)
  rw [ammPC1466] at h; simpa using h
@[simp] theorem ammPC1468 :
    Artifact.submissionArtifact.instructionPC 1468 = 1989 := by
  have h := pcSuccOp (index := 1467) (by rfl)
  rw [ammPC1467] at h; simpa using h
@[simp] theorem ammPC1469 :
    Artifact.submissionArtifact.instructionPC 1469 = 1990 := by
  have h := pcSuccOp (index := 1468) (by rfl)
  rw [ammPC1468] at h; simpa using h
@[simp] theorem ammPC1470 :
    Artifact.submissionArtifact.instructionPC 1470 = 1991 := by
  have h := pcSuccOp (index := 1469) (by rfl)
  rw [ammPC1469] at h; simpa using h
@[simp] theorem ammPC1471 :
    Artifact.submissionArtifact.instructionPC 1471 = 1992 := by
  have h := pcSuccOp (index := 1470) (by rfl)
  rw [ammPC1470] at h; simpa using h
@[simp] theorem ammPC1472 :
    Artifact.submissionArtifact.instructionPC 1472 = 1993 := by
  have h := pcSuccOp (index := 1471) (by rfl)
  rw [ammPC1471] at h; simpa using h
@[simp] theorem ammPC1473 :
    Artifact.submissionArtifact.instructionPC 1473 = 1994 := by
  have h := pcSuccOp (index := 1472) (by rfl)
  rw [ammPC1472] at h; simpa using h
@[simp] theorem ammPC1474 :
    Artifact.submissionArtifact.instructionPC 1474 = 1995 := by
  have h := pcSuccOp (index := 1473) (by rfl)
  rw [ammPC1473] at h; simpa using h
@[simp] theorem ammPC1475 :
    Artifact.submissionArtifact.instructionPC 1475 = 1997 := by
  have h := pcSuccPush (index := 1474) (by rfl)
  rw [ammPC1474] at h; simpa using h
@[simp] theorem ammPC1476 :
    Artifact.submissionArtifact.instructionPC 1476 = 1998 := by
  have h := pcSuccOp (index := 1475) (by rfl)
  rw [ammPC1475] at h; simpa using h
@[simp] theorem ammPC1477 :
    Artifact.submissionArtifact.instructionPC 1477 = 1999 := by
  have h := pcSuccOp (index := 1476) (by rfl)
  rw [ammPC1476] at h; simpa using h
@[simp] theorem ammPC1478 :
    Artifact.submissionArtifact.instructionPC 1478 = 2000 := by
  have h := pcSuccOp (index := 1477) (by rfl)
  rw [ammPC1477] at h; simpa using h
@[simp] theorem ammPC1479 :
    Artifact.submissionArtifact.instructionPC 1479 = 2001 := by
  have h := pcSuccOp (index := 1478) (by rfl)
  rw [ammPC1478] at h; simpa using h
@[simp] theorem ammPC1480 :
    Artifact.submissionArtifact.instructionPC 1480 = 2004 := by
  have h := pcSuccPush (index := 1479) (by rfl)
  rw [ammPC1479] at h; simpa using h
@[simp] theorem ammPC1481 :
    Artifact.submissionArtifact.instructionPC 1481 = 2005 := by
  have h := pcSuccOp (index := 1480) (by rfl)
  rw [ammPC1480] at h; simpa using h
@[simp] theorem ammPC1482 :
    Artifact.submissionArtifact.instructionPC 1482 = 2006 := by
  have h := pcSuccOp (index := 1481) (by rfl)
  rw [ammPC1481] at h; simpa using h
@[simp] theorem ammPC1483 :
    Artifact.submissionArtifact.instructionPC 1483 = 2007 := by
  have h := pcSuccOp (index := 1482) (by rfl)
  rw [ammPC1482] at h; simpa using h
@[simp] theorem ammPC1484 :
    Artifact.submissionArtifact.instructionPC 1484 = 2008 := by
  have h := pcSuccOp (index := 1483) (by rfl)
  rw [ammPC1483] at h; simpa using h
@[simp] theorem ammPC1485 :
    Artifact.submissionArtifact.instructionPC 1485 = 2009 := by
  have h := pcSuccOp (index := 1484) (by rfl)
  rw [ammPC1484] at h; simpa using h
@[simp] theorem ammPC1486 :
    Artifact.submissionArtifact.instructionPC 1486 = 2010 := by
  have h := pcSuccOp (index := 1485) (by rfl)
  rw [ammPC1485] at h; simpa using h
@[simp] theorem ammPC1487 :
    Artifact.submissionArtifact.instructionPC 1487 = 2011 := by
  have h := pcSuccOp (index := 1486) (by rfl)
  rw [ammPC1486] at h; simpa using h
@[simp] theorem ammPC1488 :
    Artifact.submissionArtifact.instructionPC 1488 = 2012 := by
  have h := pcSuccOp (index := 1487) (by rfl)
  rw [ammPC1487] at h; simpa using h
@[simp] theorem ammPC1489 :
    Artifact.submissionArtifact.instructionPC 1489 = 2013 := by
  have h := pcSuccOp (index := 1488) (by rfl)
  rw [ammPC1488] at h; simpa using h
@[simp] theorem ammPC1490 :
    Artifact.submissionArtifact.instructionPC 1490 = 2014 := by
  have h := pcSuccOp (index := 1489) (by rfl)
  rw [ammPC1489] at h; simpa using h
@[simp] theorem ammPC1491 :
    Artifact.submissionArtifact.instructionPC 1491 = 2015 := by
  have h := pcSuccOp (index := 1490) (by rfl)
  rw [ammPC1490] at h; simpa using h
@[simp] theorem ammPC1492 :
    Artifact.submissionArtifact.instructionPC 1492 = 2016 := by
  have h := pcSuccOp (index := 1491) (by rfl)
  rw [ammPC1491] at h; simpa using h
@[simp] theorem ammPC1493 :
    Artifact.submissionArtifact.instructionPC 1493 = 2017 := by
  have h := pcSuccOp (index := 1492) (by rfl)
  rw [ammPC1492] at h; simpa using h
@[simp] theorem ammPC1494 :
    Artifact.submissionArtifact.instructionPC 1494 = 2018 := by
  have h := pcSuccOp (index := 1493) (by rfl)
  rw [ammPC1493] at h; simpa using h

/-! ### Jump destinations of the region -/

theorem jumpAMM :
    Decode.isValidJumpDest submissionBytecode 1867 = true := by
  have h := Artifact.isValidJumpDest_index 1356 (by rfl)
  simpa [Artifact.instructionPC, ammPC1356] using h

theorem jumpAMM_LOOP :
    Decode.isValidJumpDest submissionBytecode 1894 = true := by
  have h := Artifact.isValidJumpDest_index 1380 (by rfl)
  simpa [Artifact.instructionPC, ammPC1380] using h

theorem jumpAMM_DECIDE :
    Decode.isValidJumpDest submissionBytecode 1947 = true := by
  have h := Artifact.isValidJumpDest_index 1430 (by rfl)
  simpa [Artifact.instructionPC, ammPC1430] using h

theorem jumpAMM_SUB :
    Decode.isValidJumpDest submissionBytecode 1971 = true := by
  have h := Artifact.isValidJumpDest_index 1450 (by rfl)
  simpa [Artifact.instructionPC, ammPC1450] using h

theorem jumpAMM_EXIT :
    Decode.isValidJumpDest submissionBytecode 2005 = true := by
  have h := Artifact.isValidJumpDest_index 1481 (by rfl)
  simpa [Artifact.instructionPC, ammPC1481] using h

end Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
