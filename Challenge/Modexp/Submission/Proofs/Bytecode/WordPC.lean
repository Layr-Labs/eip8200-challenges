import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Instruction offsets for the `modexpWord` region

`ProgramArtifact.instructionPC index` assembles the first `index` instructions,
so proving one `decide` per index is quadratic and, at indices past 1500, costs
seconds each.  `pcStep` derives offset `index + 1` from offset `index` and the
width of one instruction, so a single seed plus a chain is linear.  The table
lives in its own module so that the edit-compile loop of the block layer never
pays for it.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordPC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem pcStep {i n w m : Nat} {x : YulEvmCompiler.Instr}
    (hprev : Artifact.submissionArtifact.instructionPC i = n)
    (hget : Artifact.submissionInstructions[i]? = some x)
    (hw : x.bytes.length = w)
    (hm : n + w = m) :
    Artifact.submissionArtifact.instructionPC (i + 1) = m := by
  have hsplit : Artifact.submissionInstructions.take (i + 1) =
      Artifact.submissionInstructions.take i ++ [x] := by
    rw [List.take_add_one, hget]
    rfl
  show (YulEvmCompiler.assembleBytes
    (Artifact.submissionInstructions.take (i + 1))).length = m
  rw [hsplit, YulEvmCompiler.assembleBytes_append, List.length_append]
  show (YulEvmCompiler.assembleBytes
    (Artifact.submissionInstructions.take i)).length +
      (YulEvmCompiler.assembleBytes [x]).length = m
  rw [show (YulEvmCompiler.assembleBytes
      (Artifact.submissionInstructions.take i)).length = n from hprev,
    show (YulEvmCompiler.assembleBytes [x]).length = w from by
      simpa [YulEvmCompiler.assembleBytes] using hw]
  exact hm

@[simp] theorem pc415 :
    Artifact.submissionArtifact.instructionPC 415 = 517 := by decide
@[simp] theorem pc416 :
    Artifact.submissionArtifact.instructionPC 416 = 518 :=
  pcStep pc415 rfl rfl rfl
@[simp] theorem pc417 :
    Artifact.submissionArtifact.instructionPC 417 = 519 :=
  pcStep pc416 rfl rfl rfl
@[simp] theorem pc418 :
    Artifact.submissionArtifact.instructionPC 418 = 520 :=
  pcStep pc417 rfl rfl rfl
@[simp] theorem pc419 :
    Artifact.submissionArtifact.instructionPC 419 = 521 :=
  pcStep pc418 rfl rfl rfl
@[simp] theorem pc420 :
    Artifact.submissionArtifact.instructionPC 420 = 523 :=
  pcStep pc419 rfl rfl rfl
@[simp] theorem pc421 :
    Artifact.submissionArtifact.instructionPC 421 = 524 :=
  pcStep pc420 rfl rfl rfl
@[simp] theorem pc422 :
    Artifact.submissionArtifact.instructionPC 422 = 526 :=
  pcStep pc421 rfl rfl rfl
@[simp] theorem pc423 :
    Artifact.submissionArtifact.instructionPC 423 = 527 :=
  pcStep pc422 rfl rfl rfl
@[simp] theorem pc424 :
    Artifact.submissionArtifact.instructionPC 424 = 528 :=
  pcStep pc423 rfl rfl rfl
@[simp] theorem pc425 :
    Artifact.submissionArtifact.instructionPC 425 = 529 :=
  pcStep pc424 rfl rfl rfl
@[simp] theorem pc426 :
    Artifact.submissionArtifact.instructionPC 426 = 532 :=
  pcStep pc425 rfl rfl rfl
@[simp] theorem pc427 :
    Artifact.submissionArtifact.instructionPC 427 = 533 :=
  pcStep pc426 rfl rfl rfl
@[simp] theorem pc428 :
    Artifact.submissionArtifact.instructionPC 428 = 534 :=
  pcStep pc427 rfl rfl rfl
@[simp] theorem pc429 :
    Artifact.submissionArtifact.instructionPC 429 = 537 :=
  pcStep pc428 rfl rfl rfl
@[simp] theorem pc430 :
    Artifact.submissionArtifact.instructionPC 430 = 538 :=
  pcStep pc429 rfl rfl rfl
@[simp] theorem pc431 :
    Artifact.submissionArtifact.instructionPC 431 = 539 :=
  pcStep pc430 rfl rfl rfl
@[simp] theorem pc432 :
    Artifact.submissionArtifact.instructionPC 432 = 542 :=
  pcStep pc431 rfl rfl rfl
@[simp] theorem pc1495 :
    Artifact.submissionArtifact.instructionPC 1495 = 2019 := by decide
@[simp] theorem pc1496 :
    Artifact.submissionArtifact.instructionPC 1496 = 2020 :=
  pcStep pc1495 rfl rfl rfl
@[simp] theorem pc1497 :
    Artifact.submissionArtifact.instructionPC 1497 = 2021 :=
  pcStep pc1496 rfl rfl rfl
@[simp] theorem pc1498 :
    Artifact.submissionArtifact.instructionPC 1498 = 2022 :=
  pcStep pc1497 rfl rfl rfl
@[simp] theorem pc1499 :
    Artifact.submissionArtifact.instructionPC 1499 = 2023 :=
  pcStep pc1498 rfl rfl rfl
@[simp] theorem pc1500 :
    Artifact.submissionArtifact.instructionPC 1500 = 2024 :=
  pcStep pc1499 rfl rfl rfl
@[simp] theorem pc1501 :
    Artifact.submissionArtifact.instructionPC 1501 = 2026 :=
  pcStep pc1500 rfl rfl rfl
@[simp] theorem pc1502 :
    Artifact.submissionArtifact.instructionPC 1502 = 2027 :=
  pcStep pc1501 rfl rfl rfl
@[simp] theorem pc1503 :
    Artifact.submissionArtifact.instructionPC 1503 = 2028 :=
  pcStep pc1502 rfl rfl rfl
@[simp] theorem pc1504 :
    Artifact.submissionArtifact.instructionPC 1504 = 2029 :=
  pcStep pc1503 rfl rfl rfl
@[simp] theorem pc1505 :
    Artifact.submissionArtifact.instructionPC 1505 = 2030 :=
  pcStep pc1504 rfl rfl rfl
@[simp] theorem pc1506 :
    Artifact.submissionArtifact.instructionPC 1506 = 2032 :=
  pcStep pc1505 rfl rfl rfl
@[simp] theorem pc1507 :
    Artifact.submissionArtifact.instructionPC 1507 = 2033 :=
  pcStep pc1506 rfl rfl rfl
@[simp] theorem pc1508 :
    Artifact.submissionArtifact.instructionPC 1508 = 2035 :=
  pcStep pc1507 rfl rfl rfl
@[simp] theorem pc1509 :
    Artifact.submissionArtifact.instructionPC 1509 = 2036 :=
  pcStep pc1508 rfl rfl rfl
@[simp] theorem pc1510 :
    Artifact.submissionArtifact.instructionPC 1510 = 2037 :=
  pcStep pc1509 rfl rfl rfl
@[simp] theorem pc1511 :
    Artifact.submissionArtifact.instructionPC 1511 = 2039 :=
  pcStep pc1510 rfl rfl rfl
@[simp] theorem pc1512 :
    Artifact.submissionArtifact.instructionPC 1512 = 2040 :=
  pcStep pc1511 rfl rfl rfl
@[simp] theorem pc1513 :
    Artifact.submissionArtifact.instructionPC 1513 = 2042 :=
  pcStep pc1512 rfl rfl rfl
@[simp] theorem pc1514 :
    Artifact.submissionArtifact.instructionPC 1514 = 2043 :=
  pcStep pc1513 rfl rfl rfl
@[simp] theorem pc1515 :
    Artifact.submissionArtifact.instructionPC 1515 = 2044 :=
  pcStep pc1514 rfl rfl rfl
@[simp] theorem pc1516 :
    Artifact.submissionArtifact.instructionPC 1516 = 2045 :=
  pcStep pc1515 rfl rfl rfl
@[simp] theorem pc1517 :
    Artifact.submissionArtifact.instructionPC 1517 = 2046 :=
  pcStep pc1516 rfl rfl rfl
@[simp] theorem pc1518 :
    Artifact.submissionArtifact.instructionPC 1518 = 2047 :=
  pcStep pc1517 rfl rfl rfl
@[simp] theorem pc1519 :
    Artifact.submissionArtifact.instructionPC 1519 = 2048 :=
  pcStep pc1518 rfl rfl rfl
@[simp] theorem pc1520 :
    Artifact.submissionArtifact.instructionPC 1520 = 2050 :=
  pcStep pc1519 rfl rfl rfl
@[simp] theorem pc1521 :
    Artifact.submissionArtifact.instructionPC 1521 = 2051 :=
  pcStep pc1520 rfl rfl rfl
@[simp] theorem pc1522 :
    Artifact.submissionArtifact.instructionPC 1522 = 2052 :=
  pcStep pc1521 rfl rfl rfl
@[simp] theorem pc1523 :
    Artifact.submissionArtifact.instructionPC 1523 = 2053 :=
  pcStep pc1522 rfl rfl rfl
@[simp] theorem pc1524 :
    Artifact.submissionArtifact.instructionPC 1524 = 2054 :=
  pcStep pc1523 rfl rfl rfl
@[simp] theorem pc1525 :
    Artifact.submissionArtifact.instructionPC 1525 = 2055 :=
  pcStep pc1524 rfl rfl rfl
@[simp] theorem pc1526 :
    Artifact.submissionArtifact.instructionPC 1526 = 2056 :=
  pcStep pc1525 rfl rfl rfl
@[simp] theorem pc1527 :
    Artifact.submissionArtifact.instructionPC 1527 = 2059 :=
  pcStep pc1526 rfl rfl rfl
@[simp] theorem pc1528 :
    Artifact.submissionArtifact.instructionPC 1528 = 2060 :=
  pcStep pc1527 rfl rfl rfl
@[simp] theorem pc1529 :
    Artifact.submissionArtifact.instructionPC 1529 = 2061 :=
  pcStep pc1528 rfl rfl rfl
@[simp] theorem pc1530 :
    Artifact.submissionArtifact.instructionPC 1530 = 2062 :=
  pcStep pc1529 rfl rfl rfl
@[simp] theorem pc1531 :
    Artifact.submissionArtifact.instructionPC 1531 = 2063 :=
  pcStep pc1530 rfl rfl rfl
@[simp] theorem pc1532 :
    Artifact.submissionArtifact.instructionPC 1532 = 2064 :=
  pcStep pc1531 rfl rfl rfl
@[simp] theorem pc1533 :
    Artifact.submissionArtifact.instructionPC 1533 = 2065 :=
  pcStep pc1532 rfl rfl rfl
@[simp] theorem pc1534 :
    Artifact.submissionArtifact.instructionPC 1534 = 2066 :=
  pcStep pc1533 rfl rfl rfl
@[simp] theorem pc1535 :
    Artifact.submissionArtifact.instructionPC 1535 = 2067 :=
  pcStep pc1534 rfl rfl rfl
@[simp] theorem pc1536 :
    Artifact.submissionArtifact.instructionPC 1536 = 2068 :=
  pcStep pc1535 rfl rfl rfl
@[simp] theorem pc1537 :
    Artifact.submissionArtifact.instructionPC 1537 = 2069 :=
  pcStep pc1536 rfl rfl rfl
@[simp] theorem pc1538 :
    Artifact.submissionArtifact.instructionPC 1538 = 2070 :=
  pcStep pc1537 rfl rfl rfl
@[simp] theorem pc1539 :
    Artifact.submissionArtifact.instructionPC 1539 = 2071 :=
  pcStep pc1538 rfl rfl rfl
@[simp] theorem pc1540 :
    Artifact.submissionArtifact.instructionPC 1540 = 2072 :=
  pcStep pc1539 rfl rfl rfl
@[simp] theorem pc1541 :
    Artifact.submissionArtifact.instructionPC 1541 = 2074 :=
  pcStep pc1540 rfl rfl rfl
@[simp] theorem pc1542 :
    Artifact.submissionArtifact.instructionPC 1542 = 2075 :=
  pcStep pc1541 rfl rfl rfl
@[simp] theorem pc1543 :
    Artifact.submissionArtifact.instructionPC 1543 = 2078 :=
  pcStep pc1542 rfl rfl rfl
@[simp] theorem pc1544 :
    Artifact.submissionArtifact.instructionPC 1544 = 2079 :=
  pcStep pc1543 rfl rfl rfl
@[simp] theorem pc1545 :
    Artifact.submissionArtifact.instructionPC 1545 = 2080 :=
  pcStep pc1544 rfl rfl rfl
@[simp] theorem pc1546 :
    Artifact.submissionArtifact.instructionPC 1546 = 2081 :=
  pcStep pc1545 rfl rfl rfl
@[simp] theorem pc1547 :
    Artifact.submissionArtifact.instructionPC 1547 = 2082 :=
  pcStep pc1546 rfl rfl rfl
@[simp] theorem pc1548 :
    Artifact.submissionArtifact.instructionPC 1548 = 2083 :=
  pcStep pc1547 rfl rfl rfl
@[simp] theorem pc1549 :
    Artifact.submissionArtifact.instructionPC 1549 = 2084 :=
  pcStep pc1548 rfl rfl rfl
@[simp] theorem pc1550 :
    Artifact.submissionArtifact.instructionPC 1550 = 2086 :=
  pcStep pc1549 rfl rfl rfl
@[simp] theorem pc1551 :
    Artifact.submissionArtifact.instructionPC 1551 = 2087 :=
  pcStep pc1550 rfl rfl rfl
@[simp] theorem pc1552 :
    Artifact.submissionArtifact.instructionPC 1552 = 2088 :=
  pcStep pc1551 rfl rfl rfl
@[simp] theorem pc1553 :
    Artifact.submissionArtifact.instructionPC 1553 = 2089 :=
  pcStep pc1552 rfl rfl rfl
@[simp] theorem pc1554 :
    Artifact.submissionArtifact.instructionPC 1554 = 2090 :=
  pcStep pc1553 rfl rfl rfl
@[simp] theorem pc1555 :
    Artifact.submissionArtifact.instructionPC 1555 = 2092 :=
  pcStep pc1554 rfl rfl rfl
@[simp] theorem pc1556 :
    Artifact.submissionArtifact.instructionPC 1556 = 2093 :=
  pcStep pc1555 rfl rfl rfl
@[simp] theorem pc1557 :
    Artifact.submissionArtifact.instructionPC 1557 = 2094 :=
  pcStep pc1556 rfl rfl rfl
@[simp] theorem pc1558 :
    Artifact.submissionArtifact.instructionPC 1558 = 2095 :=
  pcStep pc1557 rfl rfl rfl
@[simp] theorem pc1559 :
    Artifact.submissionArtifact.instructionPC 1559 = 2096 :=
  pcStep pc1558 rfl rfl rfl
@[simp] theorem pc1560 :
    Artifact.submissionArtifact.instructionPC 1560 = 2097 :=
  pcStep pc1559 rfl rfl rfl
@[simp] theorem pc1561 :
    Artifact.submissionArtifact.instructionPC 1561 = 2098 :=
  pcStep pc1560 rfl rfl rfl
@[simp] theorem pc1562 :
    Artifact.submissionArtifact.instructionPC 1562 = 2099 :=
  pcStep pc1561 rfl rfl rfl
@[simp] theorem pc1563 :
    Artifact.submissionArtifact.instructionPC 1563 = 2101 :=
  pcStep pc1562 rfl rfl rfl
@[simp] theorem pc1564 :
    Artifact.submissionArtifact.instructionPC 1564 = 2102 :=
  pcStep pc1563 rfl rfl rfl
@[simp] theorem pc1565 :
    Artifact.submissionArtifact.instructionPC 1565 = 2103 :=
  pcStep pc1564 rfl rfl rfl
@[simp] theorem pc1566 :
    Artifact.submissionArtifact.instructionPC 1566 = 2104 :=
  pcStep pc1565 rfl rfl rfl
@[simp] theorem pc1567 :
    Artifact.submissionArtifact.instructionPC 1567 = 2105 :=
  pcStep pc1566 rfl rfl rfl
@[simp] theorem pc1568 :
    Artifact.submissionArtifact.instructionPC 1568 = 2106 :=
  pcStep pc1567 rfl rfl rfl
@[simp] theorem pc1569 :
    Artifact.submissionArtifact.instructionPC 1569 = 2107 :=
  pcStep pc1568 rfl rfl rfl
@[simp] theorem pc1570 :
    Artifact.submissionArtifact.instructionPC 1570 = 2109 :=
  pcStep pc1569 rfl rfl rfl
@[simp] theorem pc1571 :
    Artifact.submissionArtifact.instructionPC 1571 = 2110 :=
  pcStep pc1570 rfl rfl rfl
@[simp] theorem pc1572 :
    Artifact.submissionArtifact.instructionPC 1572 = 2111 :=
  pcStep pc1571 rfl rfl rfl
@[simp] theorem pc1573 :
    Artifact.submissionArtifact.instructionPC 1573 = 2112 :=
  pcStep pc1572 rfl rfl rfl
@[simp] theorem pc1574 :
    Artifact.submissionArtifact.instructionPC 1574 = 2113 :=
  pcStep pc1573 rfl rfl rfl
@[simp] theorem pc1575 :
    Artifact.submissionArtifact.instructionPC 1575 = 2114 :=
  pcStep pc1574 rfl rfl rfl
@[simp] theorem pc1576 :
    Artifact.submissionArtifact.instructionPC 1576 = 2115 :=
  pcStep pc1575 rfl rfl rfl
@[simp] theorem pc1577 :
    Artifact.submissionArtifact.instructionPC 1577 = 2117 :=
  pcStep pc1576 rfl rfl rfl
@[simp] theorem pc1578 :
    Artifact.submissionArtifact.instructionPC 1578 = 2118 :=
  pcStep pc1577 rfl rfl rfl
@[simp] theorem pc1579 :
    Artifact.submissionArtifact.instructionPC 1579 = 2119 :=
  pcStep pc1578 rfl rfl rfl
@[simp] theorem pc1580 :
    Artifact.submissionArtifact.instructionPC 1580 = 2120 :=
  pcStep pc1579 rfl rfl rfl
@[simp] theorem pc1581 :
    Artifact.submissionArtifact.instructionPC 1581 = 2121 :=
  pcStep pc1580 rfl rfl rfl
@[simp] theorem pc1582 :
    Artifact.submissionArtifact.instructionPC 1582 = 2122 :=
  pcStep pc1581 rfl rfl rfl
@[simp] theorem pc1583 :
    Artifact.submissionArtifact.instructionPC 1583 = 2123 :=
  pcStep pc1582 rfl rfl rfl
@[simp] theorem pc1584 :
    Artifact.submissionArtifact.instructionPC 1584 = 2125 :=
  pcStep pc1583 rfl rfl rfl
@[simp] theorem pc1585 :
    Artifact.submissionArtifact.instructionPC 1585 = 2126 :=
  pcStep pc1584 rfl rfl rfl
@[simp] theorem pc1586 :
    Artifact.submissionArtifact.instructionPC 1586 = 2127 :=
  pcStep pc1585 rfl rfl rfl
@[simp] theorem pc1587 :
    Artifact.submissionArtifact.instructionPC 1587 = 2128 :=
  pcStep pc1586 rfl rfl rfl
@[simp] theorem pc1588 :
    Artifact.submissionArtifact.instructionPC 1588 = 2129 :=
  pcStep pc1587 rfl rfl rfl
@[simp] theorem pc1589 :
    Artifact.submissionArtifact.instructionPC 1589 = 2130 :=
  pcStep pc1588 rfl rfl rfl
@[simp] theorem pc1590 :
    Artifact.submissionArtifact.instructionPC 1590 = 2131 :=
  pcStep pc1589 rfl rfl rfl
@[simp] theorem pc1591 :
    Artifact.submissionArtifact.instructionPC 1591 = 2133 :=
  pcStep pc1590 rfl rfl rfl
@[simp] theorem pc1592 :
    Artifact.submissionArtifact.instructionPC 1592 = 2134 :=
  pcStep pc1591 rfl rfl rfl
@[simp] theorem pc1593 :
    Artifact.submissionArtifact.instructionPC 1593 = 2135 :=
  pcStep pc1592 rfl rfl rfl
@[simp] theorem pc1594 :
    Artifact.submissionArtifact.instructionPC 1594 = 2136 :=
  pcStep pc1593 rfl rfl rfl
@[simp] theorem pc1595 :
    Artifact.submissionArtifact.instructionPC 1595 = 2137 :=
  pcStep pc1594 rfl rfl rfl
@[simp] theorem pc1596 :
    Artifact.submissionArtifact.instructionPC 1596 = 2138 :=
  pcStep pc1595 rfl rfl rfl
@[simp] theorem pc1597 :
    Artifact.submissionArtifact.instructionPC 1597 = 2139 :=
  pcStep pc1596 rfl rfl rfl
@[simp] theorem pc1598 :
    Artifact.submissionArtifact.instructionPC 1598 = 2141 :=
  pcStep pc1597 rfl rfl rfl
@[simp] theorem pc1599 :
    Artifact.submissionArtifact.instructionPC 1599 = 2142 :=
  pcStep pc1598 rfl rfl rfl
@[simp] theorem pc1600 :
    Artifact.submissionArtifact.instructionPC 1600 = 2143 :=
  pcStep pc1599 rfl rfl rfl
@[simp] theorem pc1601 :
    Artifact.submissionArtifact.instructionPC 1601 = 2144 :=
  pcStep pc1600 rfl rfl rfl
@[simp] theorem pc1602 :
    Artifact.submissionArtifact.instructionPC 1602 = 2145 :=
  pcStep pc1601 rfl rfl rfl
@[simp] theorem pc1603 :
    Artifact.submissionArtifact.instructionPC 1603 = 2146 :=
  pcStep pc1602 rfl rfl rfl
@[simp] theorem pc1604 :
    Artifact.submissionArtifact.instructionPC 1604 = 2147 :=
  pcStep pc1603 rfl rfl rfl
@[simp] theorem pc1605 :
    Artifact.submissionArtifact.instructionPC 1605 = 2150 :=
  pcStep pc1604 rfl rfl rfl
@[simp] theorem pc1606 :
    Artifact.submissionArtifact.instructionPC 1606 = 2151 :=
  pcStep pc1605 rfl rfl rfl
@[simp] theorem pc1607 :
    Artifact.submissionArtifact.instructionPC 1607 = 2152 :=
  pcStep pc1606 rfl rfl rfl
@[simp] theorem pc1608 :
    Artifact.submissionArtifact.instructionPC 1608 = 2153 :=
  pcStep pc1607 rfl rfl rfl
@[simp] theorem pc1609 :
    Artifact.submissionArtifact.instructionPC 1609 = 2154 :=
  pcStep pc1608 rfl rfl rfl
@[simp] theorem pc1610 :
    Artifact.submissionArtifact.instructionPC 1610 = 2155 :=
  pcStep pc1609 rfl rfl rfl
@[simp] theorem pc1611 :
    Artifact.submissionArtifact.instructionPC 1611 = 2156 :=
  pcStep pc1610 rfl rfl rfl
@[simp] theorem pc1612 :
    Artifact.submissionArtifact.instructionPC 1612 = 2159 :=
  pcStep pc1611 rfl rfl rfl
@[simp] theorem pc1613 :
    Artifact.submissionArtifact.instructionPC 1613 = 2160 :=
  pcStep pc1612 rfl rfl rfl
@[simp] theorem pc1614 :
    Artifact.submissionArtifact.instructionPC 1614 = 2161 :=
  pcStep pc1613 rfl rfl rfl
@[simp] theorem pc1615 :
    Artifact.submissionArtifact.instructionPC 1615 = 2162 :=
  pcStep pc1614 rfl rfl rfl
@[simp] theorem pc1616 :
    Artifact.submissionArtifact.instructionPC 1616 = 2163 :=
  pcStep pc1615 rfl rfl rfl
@[simp] theorem pc1617 :
    Artifact.submissionArtifact.instructionPC 1617 = 2164 :=
  pcStep pc1616 rfl rfl rfl
@[simp] theorem pc1618 :
    Artifact.submissionArtifact.instructionPC 1618 = 2165 :=
  pcStep pc1617 rfl rfl rfl
@[simp] theorem pc1619 :
    Artifact.submissionArtifact.instructionPC 1619 = 2168 :=
  pcStep pc1618 rfl rfl rfl
@[simp] theorem pc1620 :
    Artifact.submissionArtifact.instructionPC 1620 = 2169 :=
  pcStep pc1619 rfl rfl rfl
@[simp] theorem pc1621 :
    Artifact.submissionArtifact.instructionPC 1621 = 2170 :=
  pcStep pc1620 rfl rfl rfl
@[simp] theorem pc1622 :
    Artifact.submissionArtifact.instructionPC 1622 = 2171 :=
  pcStep pc1621 rfl rfl rfl
@[simp] theorem pc1623 :
    Artifact.submissionArtifact.instructionPC 1623 = 2172 :=
  pcStep pc1622 rfl rfl rfl
@[simp] theorem pc1624 :
    Artifact.submissionArtifact.instructionPC 1624 = 2173 :=
  pcStep pc1623 rfl rfl rfl
@[simp] theorem pc1625 :
    Artifact.submissionArtifact.instructionPC 1625 = 2174 :=
  pcStep pc1624 rfl rfl rfl
@[simp] theorem pc1626 :
    Artifact.submissionArtifact.instructionPC 1626 = 2177 :=
  pcStep pc1625 rfl rfl rfl
@[simp] theorem pc1627 :
    Artifact.submissionArtifact.instructionPC 1627 = 2178 :=
  pcStep pc1626 rfl rfl rfl
@[simp] theorem pc1628 :
    Artifact.submissionArtifact.instructionPC 1628 = 2179 :=
  pcStep pc1627 rfl rfl rfl
@[simp] theorem pc1629 :
    Artifact.submissionArtifact.instructionPC 1629 = 2180 :=
  pcStep pc1628 rfl rfl rfl
@[simp] theorem pc1630 :
    Artifact.submissionArtifact.instructionPC 1630 = 2181 :=
  pcStep pc1629 rfl rfl rfl
@[simp] theorem pc1631 :
    Artifact.submissionArtifact.instructionPC 1631 = 2182 :=
  pcStep pc1630 rfl rfl rfl
@[simp] theorem pc1632 :
    Artifact.submissionArtifact.instructionPC 1632 = 2183 :=
  pcStep pc1631 rfl rfl rfl
@[simp] theorem pc1633 :
    Artifact.submissionArtifact.instructionPC 1633 = 2186 :=
  pcStep pc1632 rfl rfl rfl
@[simp] theorem pc1634 :
    Artifact.submissionArtifact.instructionPC 1634 = 2187 :=
  pcStep pc1633 rfl rfl rfl
@[simp] theorem pc1635 :
    Artifact.submissionArtifact.instructionPC 1635 = 2188 :=
  pcStep pc1634 rfl rfl rfl
@[simp] theorem pc1636 :
    Artifact.submissionArtifact.instructionPC 1636 = 2189 :=
  pcStep pc1635 rfl rfl rfl
@[simp] theorem pc1637 :
    Artifact.submissionArtifact.instructionPC 1637 = 2190 :=
  pcStep pc1636 rfl rfl rfl
@[simp] theorem pc1638 :
    Artifact.submissionArtifact.instructionPC 1638 = 2191 :=
  pcStep pc1637 rfl rfl rfl
@[simp] theorem pc1639 :
    Artifact.submissionArtifact.instructionPC 1639 = 2192 :=
  pcStep pc1638 rfl rfl rfl
@[simp] theorem pc1640 :
    Artifact.submissionArtifact.instructionPC 1640 = 2195 :=
  pcStep pc1639 rfl rfl rfl
@[simp] theorem pc1641 :
    Artifact.submissionArtifact.instructionPC 1641 = 2196 :=
  pcStep pc1640 rfl rfl rfl
@[simp] theorem pc1642 :
    Artifact.submissionArtifact.instructionPC 1642 = 2197 :=
  pcStep pc1641 rfl rfl rfl
@[simp] theorem pc1643 :
    Artifact.submissionArtifact.instructionPC 1643 = 2198 :=
  pcStep pc1642 rfl rfl rfl
@[simp] theorem pc1644 :
    Artifact.submissionArtifact.instructionPC 1644 = 2199 :=
  pcStep pc1643 rfl rfl rfl
@[simp] theorem pc1645 :
    Artifact.submissionArtifact.instructionPC 1645 = 2200 :=
  pcStep pc1644 rfl rfl rfl
@[simp] theorem pc1646 :
    Artifact.submissionArtifact.instructionPC 1646 = 2201 :=
  pcStep pc1645 rfl rfl rfl
@[simp] theorem pc1647 :
    Artifact.submissionArtifact.instructionPC 1647 = 2204 :=
  pcStep pc1646 rfl rfl rfl
@[simp] theorem pc1648 :
    Artifact.submissionArtifact.instructionPC 1648 = 2205 :=
  pcStep pc1647 rfl rfl rfl
@[simp] theorem pc1649 :
    Artifact.submissionArtifact.instructionPC 1649 = 2206 :=
  pcStep pc1648 rfl rfl rfl
@[simp] theorem pc1650 :
    Artifact.submissionArtifact.instructionPC 1650 = 2207 :=
  pcStep pc1649 rfl rfl rfl
@[simp] theorem pc1651 :
    Artifact.submissionArtifact.instructionPC 1651 = 2208 :=
  pcStep pc1650 rfl rfl rfl
@[simp] theorem pc1652 :
    Artifact.submissionArtifact.instructionPC 1652 = 2209 :=
  pcStep pc1651 rfl rfl rfl
@[simp] theorem pc1653 :
    Artifact.submissionArtifact.instructionPC 1653 = 2210 :=
  pcStep pc1652 rfl rfl rfl
@[simp] theorem pc1654 :
    Artifact.submissionArtifact.instructionPC 1654 = 2213 :=
  pcStep pc1653 rfl rfl rfl
@[simp] theorem pc1655 :
    Artifact.submissionArtifact.instructionPC 1655 = 2214 :=
  pcStep pc1654 rfl rfl rfl
@[simp] theorem pc1656 :
    Artifact.submissionArtifact.instructionPC 1656 = 2215 :=
  pcStep pc1655 rfl rfl rfl
@[simp] theorem pc1657 :
    Artifact.submissionArtifact.instructionPC 1657 = 2216 :=
  pcStep pc1656 rfl rfl rfl
@[simp] theorem pc1658 :
    Artifact.submissionArtifact.instructionPC 1658 = 2217 :=
  pcStep pc1657 rfl rfl rfl
@[simp] theorem pc1659 :
    Artifact.submissionArtifact.instructionPC 1659 = 2218 :=
  pcStep pc1658 rfl rfl rfl
@[simp] theorem pc1660 :
    Artifact.submissionArtifact.instructionPC 1660 = 2219 :=
  pcStep pc1659 rfl rfl rfl
@[simp] theorem pc1661 :
    Artifact.submissionArtifact.instructionPC 1661 = 2220 :=
  pcStep pc1660 rfl rfl rfl
@[simp] theorem pc1662 :
    Artifact.submissionArtifact.instructionPC 1662 = 2221 :=
  pcStep pc1661 rfl rfl rfl
@[simp] theorem pc1663 :
    Artifact.submissionArtifact.instructionPC 1663 = 2222 :=
  pcStep pc1662 rfl rfl rfl
@[simp] theorem pc1664 :
    Artifact.submissionArtifact.instructionPC 1664 = 2223 :=
  pcStep pc1663 rfl rfl rfl
@[simp] theorem pc1665 :
    Artifact.submissionArtifact.instructionPC 1665 = 2224 :=
  pcStep pc1664 rfl rfl rfl
@[simp] theorem pc1666 :
    Artifact.submissionArtifact.instructionPC 1666 = 2225 :=
  pcStep pc1665 rfl rfl rfl
@[simp] theorem pc1667 :
    Artifact.submissionArtifact.instructionPC 1667 = 2228 :=
  pcStep pc1666 rfl rfl rfl
@[simp] theorem pc1668 :
    Artifact.submissionArtifact.instructionPC 1668 = 2229 :=
  pcStep pc1667 rfl rfl rfl
@[simp] theorem pc1669 :
    Artifact.submissionArtifact.instructionPC 1669 = 2230 :=
  pcStep pc1668 rfl rfl rfl
@[simp] theorem pc1670 :
    Artifact.submissionArtifact.instructionPC 1670 = 2231 :=
  pcStep pc1669 rfl rfl rfl
@[simp] theorem pc1671 :
    Artifact.submissionArtifact.instructionPC 1671 = 2232 :=
  pcStep pc1670 rfl rfl rfl
@[simp] theorem pc1672 :
    Artifact.submissionArtifact.instructionPC 1672 = 2233 :=
  pcStep pc1671 rfl rfl rfl
@[simp] theorem pc1673 :
    Artifact.submissionArtifact.instructionPC 1673 = 2234 :=
  pcStep pc1672 rfl rfl rfl
@[simp] theorem pc1674 :
    Artifact.submissionArtifact.instructionPC 1674 = 2235 :=
  pcStep pc1673 rfl rfl rfl
@[simp] theorem pc1675 :
    Artifact.submissionArtifact.instructionPC 1675 = 2236 :=
  pcStep pc1674 rfl rfl rfl
@[simp] theorem pc1676 :
    Artifact.submissionArtifact.instructionPC 1676 = 2237 :=
  pcStep pc1675 rfl rfl rfl
@[simp] theorem pc1677 :
    Artifact.submissionArtifact.instructionPC 1677 = 2238 :=
  pcStep pc1676 rfl rfl rfl
@[simp] theorem pc1678 :
    Artifact.submissionArtifact.instructionPC 1678 = 2239 :=
  pcStep pc1677 rfl rfl rfl
@[simp] theorem pc1679 :
    Artifact.submissionArtifact.instructionPC 1679 = 2240 :=
  pcStep pc1678 rfl rfl rfl
@[simp] theorem pc1680 :
    Artifact.submissionArtifact.instructionPC 1680 = 2241 :=
  pcStep pc1679 rfl rfl rfl
@[simp] theorem pc1681 :
    Artifact.submissionArtifact.instructionPC 1681 = 2242 :=
  pcStep pc1680 rfl rfl rfl
@[simp] theorem pc1682 :
    Artifact.submissionArtifact.instructionPC 1682 = 2243 :=
  pcStep pc1681 rfl rfl rfl
@[simp] theorem pc1683 :
    Artifact.submissionArtifact.instructionPC 1683 = 2244 :=
  pcStep pc1682 rfl rfl rfl
@[simp] theorem pc1684 :
    Artifact.submissionArtifact.instructionPC 1684 = 2245 :=
  pcStep pc1683 rfl rfl rfl
@[simp] theorem pc1685 :
    Artifact.submissionArtifact.instructionPC 1685 = 2246 :=
  pcStep pc1684 rfl rfl rfl
@[simp] theorem pc1686 :
    Artifact.submissionArtifact.instructionPC 1686 = 2247 :=
  pcStep pc1685 rfl rfl rfl
@[simp] theorem pc1687 :
    Artifact.submissionArtifact.instructionPC 1687 = 2248 :=
  pcStep pc1686 rfl rfl rfl
@[simp] theorem pc1688 :
    Artifact.submissionArtifact.instructionPC 1688 = 2249 :=
  pcStep pc1687 rfl rfl rfl
@[simp] theorem pc1689 :
    Artifact.submissionArtifact.instructionPC 1689 = 2250 :=
  pcStep pc1688 rfl rfl rfl
@[simp] theorem pc1690 :
    Artifact.submissionArtifact.instructionPC 1690 = 2251 :=
  pcStep pc1689 rfl rfl rfl
@[simp] theorem pc1691 :
    Artifact.submissionArtifact.instructionPC 1691 = 2252 :=
  pcStep pc1690 rfl rfl rfl
@[simp] theorem pc1692 :
    Artifact.submissionArtifact.instructionPC 1692 = 2254 :=
  pcStep pc1691 rfl rfl rfl
@[simp] theorem pc1693 :
    Artifact.submissionArtifact.instructionPC 1693 = 2255 :=
  pcStep pc1692 rfl rfl rfl
@[simp] theorem pc1694 :
    Artifact.submissionArtifact.instructionPC 1694 = 2258 :=
  pcStep pc1693 rfl rfl rfl
@[simp] theorem pc1695 :
    Artifact.submissionArtifact.instructionPC 1695 = 2259 :=
  pcStep pc1694 rfl rfl rfl
@[simp] theorem pc1696 :
    Artifact.submissionArtifact.instructionPC 1696 = 2260 :=
  pcStep pc1695 rfl rfl rfl
@[simp] theorem pc1697 :
    Artifact.submissionArtifact.instructionPC 1697 = 2261 :=
  pcStep pc1696 rfl rfl rfl
@[simp] theorem pc1698 :
    Artifact.submissionArtifact.instructionPC 1698 = 2262 :=
  pcStep pc1697 rfl rfl rfl
@[simp] theorem pc1699 :
    Artifact.submissionArtifact.instructionPC 1699 = 2263 :=
  pcStep pc1698 rfl rfl rfl
@[simp] theorem pc1700 :
    Artifact.submissionArtifact.instructionPC 1700 = 2264 :=
  pcStep pc1699 rfl rfl rfl
@[simp] theorem pc1701 :
    Artifact.submissionArtifact.instructionPC 1701 = 2265 :=
  pcStep pc1700 rfl rfl rfl
@[simp] theorem pc1702 :
    Artifact.submissionArtifact.instructionPC 1702 = 2266 :=
  pcStep pc1701 rfl rfl rfl
@[simp] theorem pc1703 :
    Artifact.submissionArtifact.instructionPC 1703 = 2267 :=
  pcStep pc1702 rfl rfl rfl
@[simp] theorem pc1704 :
    Artifact.submissionArtifact.instructionPC 1704 = 2268 :=
  pcStep pc1703 rfl rfl rfl
@[simp] theorem pc1705 :
    Artifact.submissionArtifact.instructionPC 1705 = 2269 :=
  pcStep pc1704 rfl rfl rfl
@[simp] theorem pc1706 :
    Artifact.submissionArtifact.instructionPC 1706 = 2270 :=
  pcStep pc1705 rfl rfl rfl
@[simp] theorem pc1707 :
    Artifact.submissionArtifact.instructionPC 1707 = 2271 :=
  pcStep pc1706 rfl rfl rfl
@[simp] theorem pc1708 :
    Artifact.submissionArtifact.instructionPC 1708 = 2272 :=
  pcStep pc1707 rfl rfl rfl
@[simp] theorem pc1709 :
    Artifact.submissionArtifact.instructionPC 1709 = 2273 :=
  pcStep pc1708 rfl rfl rfl
@[simp] theorem pc1710 :
    Artifact.submissionArtifact.instructionPC 1710 = 2274 :=
  pcStep pc1709 rfl rfl rfl
@[simp] theorem pc1711 :
    Artifact.submissionArtifact.instructionPC 1711 = 2275 :=
  pcStep pc1710 rfl rfl rfl
@[simp] theorem pc1712 :
    Artifact.submissionArtifact.instructionPC 1712 = 2276 :=
  pcStep pc1711 rfl rfl rfl
@[simp] theorem pc1713 :
    Artifact.submissionArtifact.instructionPC 1713 = 2277 :=
  pcStep pc1712 rfl rfl rfl
@[simp] theorem pc1714 :
    Artifact.submissionArtifact.instructionPC 1714 = 2278 :=
  pcStep pc1713 rfl rfl rfl
@[simp] theorem pc1715 :
    Artifact.submissionArtifact.instructionPC 1715 = 2279 :=
  pcStep pc1714 rfl rfl rfl
@[simp] theorem pc1716 :
    Artifact.submissionArtifact.instructionPC 1716 = 2280 :=
  pcStep pc1715 rfl rfl rfl
@[simp] theorem pc1717 :
    Artifact.submissionArtifact.instructionPC 1717 = 2282 :=
  pcStep pc1716 rfl rfl rfl
@[simp] theorem pc1718 :
    Artifact.submissionArtifact.instructionPC 1718 = 2283 :=
  pcStep pc1717 rfl rfl rfl
@[simp] theorem pc1719 :
    Artifact.submissionArtifact.instructionPC 1719 = 2286 :=
  pcStep pc1718 rfl rfl rfl
@[simp] theorem pc1720 :
    Artifact.submissionArtifact.instructionPC 1720 = 2287 :=
  pcStep pc1719 rfl rfl rfl
@[simp] theorem pc1721 :
    Artifact.submissionArtifact.instructionPC 1721 = 2288 :=
  pcStep pc1720 rfl rfl rfl
@[simp] theorem pc1722 :
    Artifact.submissionArtifact.instructionPC 1722 = 2289 :=
  pcStep pc1721 rfl rfl rfl
@[simp] theorem pc1723 :
    Artifact.submissionArtifact.instructionPC 1723 = 2290 :=
  pcStep pc1722 rfl rfl rfl
@[simp] theorem pc1724 :
    Artifact.submissionArtifact.instructionPC 1724 = 2291 :=
  pcStep pc1723 rfl rfl rfl
@[simp] theorem pc1725 :
    Artifact.submissionArtifact.instructionPC 1725 = 2292 :=
  pcStep pc1724 rfl rfl rfl
@[simp] theorem pc1726 :
    Artifact.submissionArtifact.instructionPC 1726 = 2294 :=
  pcStep pc1725 rfl rfl rfl
@[simp] theorem pc1727 :
    Artifact.submissionArtifact.instructionPC 1727 = 2295 :=
  pcStep pc1726 rfl rfl rfl
@[simp] theorem pc1728 :
    Artifact.submissionArtifact.instructionPC 1728 = 2296 :=
  pcStep pc1727 rfl rfl rfl
@[simp] theorem pc1729 :
    Artifact.submissionArtifact.instructionPC 1729 = 2299 :=
  pcStep pc1728 rfl rfl rfl
@[simp] theorem pc1730 :
    Artifact.submissionArtifact.instructionPC 1730 = 2300 :=
  pcStep pc1729 rfl rfl rfl
@[simp] theorem pc1731 :
    Artifact.submissionArtifact.instructionPC 1731 = 2301 :=
  pcStep pc1730 rfl rfl rfl
@[simp] theorem pc1732 :
    Artifact.submissionArtifact.instructionPC 1732 = 2302 :=
  pcStep pc1731 rfl rfl rfl
@[simp] theorem pc1733 :
    Artifact.submissionArtifact.instructionPC 1733 = 2303 :=
  pcStep pc1732 rfl rfl rfl
@[simp] theorem pc1734 :
    Artifact.submissionArtifact.instructionPC 1734 = 2304 :=
  pcStep pc1733 rfl rfl rfl
@[simp] theorem pc1735 :
    Artifact.submissionArtifact.instructionPC 1735 = 2305 :=
  pcStep pc1734 rfl rfl rfl
@[simp] theorem pc1736 :
    Artifact.submissionArtifact.instructionPC 1736 = 2306 :=
  pcStep pc1735 rfl rfl rfl
@[simp] theorem pc1737 :
    Artifact.submissionArtifact.instructionPC 1737 = 2309 :=
  pcStep pc1736 rfl rfl rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WordPC
