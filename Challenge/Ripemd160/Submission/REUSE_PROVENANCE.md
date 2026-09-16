# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/fa7aec485cbeffb87af152e28d77c6e99544a419
Original submitter: @Meganpark980320
Yukon source: b328bfd0-d474-4de5-92ba-67934f030773
Executable SHA-256: 4c9bf9eb76243bb463bb8fdc711e75862ca4c23ba0f347392e4a7df11fce6938

This submission reuses that tree and its Lean proof structure, with one change of our own: six
mask-application pairs in the per-block message-table preamble, at program counters 596, 611, 616,
632, 652, 664, are replaced by `JUMPDEST ; JUMPDEST`. Each pair copied a lane mask to the top of
the stack and applied it to the value beneath it. The mask is
`0xffffffff0000000000000000000000000000ffffffff`, whose set bits are the lanes [0, 32) and [144,
176); removing it leaves the bits outside those lanes in place, which the consuming fold does not
read. The replacement keeps the artifact at the same length so that no program counter moves. 12
bytes differ between the source executable and this one, all of them inside program counters 596
to 665, and no other byte changes.

Resulting executable SHA-256: 1735dc99eb86be7b3ec397c2f79cc95a471538cec7c31d873cd96842339ac715

Earlier links, complete from the last link the source tree itself declares up to that
base, then that tree's own record reproduced verbatim:

- @ercumentyildirim, Yukon source 46434354-ffd8-4c40-9c43-f21be1c2b76d,
  commit 3d20f1d98bf9501c6d1eb13fd39e6035ac120805,
  executable a4c81cf85febbffa69cf7343598f6e90bb450bb9e572b021a2c7b968d969cf36.
- @i34-9, Yukon source 0cef0cce-ddf8-4d6e-b939-fa3b95d5c89f,
  commit db6b1045429c0c254f253291a3026c6b93fdff22,
  executable 71253c6fafa2b9dba613cc91d4220e6a8f0fb73dd30ec9dbfff108d53d849336.
- and, at and before commit 7a6785a7e139fe90f0d16f78b70221ae7926d355, the links the source tree itself declares, reproduced here verbatim from the record it carried:

  Source: https://github.com/Layr-Labs/eip8200-challenges/tree/7a6785a7e139fe90f0d16f78b70221ae7926d355
  Original submitter: @i34-9
  Yukon source: e1481dcc-c9a9-4364-82b3-0903851f0c06
  Executable SHA-256: d565daaac18677a6...

  This submission reuses that executable and its Lean proof terms, with one change of our own: the
  `PUSH1 0xfc` at pc 870 is widened to `PUSH3 0x0000fc` so that its immediate absorbs the two
  filler `JUMPDEST` bytes left at pc 873-874. Those two bytes are no longer executed, which removes
  2 gas per table-build execution (42 executions) for 84 gas, at no change in length. The removed mask
  itself is unchanged from the source executable.

  Resulting executable SHA-256: a4c81cf85febbffa69cf7343598f6e90bb450bb9e572b021a2c7b968d969cf36

The inherited copy of this file described an earlier step of this chain as the final one and named
that step's source as its source; the header above names the executable actually carried in this
tree and the executable actually submitted from it.
