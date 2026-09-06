"""Astra append-only quad specialization (campaign handoff, public PR342).

Pure candidate construction; no filesystem writes or process execution.
Preserve the promoted prefix/tail except for the two lane-entry bridges.
Not yet executed or integrated with the Lean artifact certificates.
"""

HELPERS = frozenset((2565, 2710, 2887, 3060, 3237,
                     3410, 3583, 3760, 3933, 4110))


def instruction(code: bytes, pc: int) -> tuple[int, bytes, int]:
    if not 0 <= pc < len(code):
        raise ValueError("instruction outside artifact")
    op = code[pc]
    size = 1 + (op - 0x5f if 0x60 <= op <= 0x7f else 0)
    end = pc + size
    if end > len(code):
        raise ValueError("truncated PUSH")
    return op, code[pc:end], end


def push2(value: int) -> bytes:
    if not 0 <= value < 65536:
        raise ValueError("PUSH2 relocation overflow")
    return b'\x61' + value.to_bytes(2, 'big')


def wrapper(code: bytes, start: int):
    """Recognize nine argument pushes, helper PUSH2, JUMP, return JUMPDEST."""
    pc = start
    pushes = []
    for _ in range(10):
        if pc >= len(code):
            return None
        op, raw, pc = instruction(code, pc)
        if op not in (0x60, 0x61):
            return None
        pushes.append(raw)
    if pushes[-1][0] != 0x61:
        return None
    helper = int.from_bytes(pushes[-1][1:], 'big')
    if helper not in HELPERS or code[pc:pc + 2] != b'\x56\x5b':
        return None
    ret = pc + 1
    if pushes[7] != push2(ret):
        return None
    return ret, helper, b''.join(pushes[:9])


def helper_body(code: bytes, target: int) -> bytes:
    if code[target] != 0x5b:
        raise ValueError("helper entry is not JUMPDEST")
    pc = target + 1
    start = pc
    while True:
        op, _, end = instruction(code, pc)
        if op == 0x56:
            return code[start:pc]
        if op in (0x00, 0x57, 0x5b, 0xf3, 0xfd, 0xfe, 0xff):
            raise ValueError("helper is not a straight-line quad")
        pc = end


def specialize(original: bytes) -> tuple[bytes, tuple[dict, ...]]:
    """Construct two append-only lanes with retained return tokens and POPs.

    Fail closed unless the source contains exactly two complete 20-quad lanes.
    Every old continuation address and every original helper remains in place.
    The caller must regenerate frozen bytes and located Lean certificates before
    packaging; this function alone is not an eligible submission.
    """
    wrappers = {}
    pc = 0
    while pc < len(original):
        found = wrapper(original, pc) if original[pc] in (0x60, 0x61) else None
        if found is not None:
            wrappers[pc] = found
        _, _, pc = instruction(original, pc)
    if len(wrappers) != 40:
        raise ValueError(f"expected 40 wrappers, found {len(wrappers)}")
    continuations = {ret + 1 for ret, _, _ in wrappers.values()}
    starts = sorted(set(wrappers) - continuations)
    if len(starts) != 2:
        raise ValueError("expected exactly two lane entries")
    result = bytearray(original)
    receipts = []
    used = set()
    for start in starts:
        pc = start
        lane = bytearray(b'\x5b')
        count = 0
        while pc in wrappers:
            if pc in used:
                raise ValueError("overlapping lanes")
            used.add(pc)
            ret, helper, arguments = wrappers[pc]
            lane.extend(arguments)
            lane.extend(helper_body(original, helper))
            lane.append(0x50)  # consume the retained return token, not JUMP
            count += 1
            pc = ret + 1
        if count != 20:
            raise ValueError(f"expected 20 quads in lane, found {count}")
        lane.extend(push2(ret))
        lane.append(0x56)
        appended_pc = len(result)
        bridge = push2(appended_pc) + b'\x56'
        result[start:start + len(bridge)] = bridge
        result.extend(lane)
        receipts.append(dict(old_entry=start, new_entry=appended_pc,
                             continuation=ret, quads=count, bytes=len(lane)))
    if used != set(wrappers):
        raise ValueError("unaccounted wrapper")
    return bytes(result), tuple(receipts)
