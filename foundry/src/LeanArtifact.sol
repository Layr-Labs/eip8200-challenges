// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Vm} from "forge-std/Vm.sol";

/// @title LeanArtifact
/// @notice Loads a challenge's frozen reference bytecode and proves, inside
///         Foundry, that the loaded bytes are the ones the Lean proof is about.
///
/// @dev Reading `Reference/reference.hex` alone would only show that the suite
///      executes *a* file in the challenge directory. The Lean proof does not
///      target that file directly: `Bytecode.lean` defines
///      `referenceBytecode := referenceBytes`, and `referenceBytes` is the byte
///      literal spelled out in `Bytes.lean`. `Correct referenceBytecode` is
///      therefore a statement about the literal.
///
///      `load` closes that gap without leaving Foundry. It reads all three
///      artifacts and requires them to agree:
///
///      * `reference.hex`, parsed to the bytes the probe etches and executes;
///      * `Bytes.lean`, parsed by walking every `abbrev referenceChunk<N>`
///        literal and concatenating the chunks in the order the `referenceBytes`
///        body concatenates them, which must equal the hex file byte for byte;
///      * `Bytecode.lean`, which must still define `referenceBytecode` as
///        `referenceBytes` and must still `include_str "reference.hex"`, so the
///        two files remain the two faces of one artifact; and
///      * the sizes proved by `referenceBytes_size` and
///        `referenceBytecode_size`, which must equal the loaded byte length.
///
///      Any drift — a regenerated hex file, an edited literal, a renamed
///      definition, a reordered concatenation — fails the load, so a gas number
///      can never be reported for bytes the proof does not cover.
library LeanArtifact {
    struct Pin {
        bytes code;
        uint256 chunkCount;
        uint256 provedSize;
    }

    string private constant CHUNK_DECL = "abbrev referenceChunk";
    string private constant CHUNK_REF = "referenceChunk";
    string private constant LITERAL_OPEN = "ByteArray.mk #[";
    string private constant BYTES_DECL = "abbrev referenceBytes : ByteArray :=";

    /// @notice Loads and pins the reference artifact in `referenceDir`.
    /// @param referenceDir Path to a `Reference/` directory, relative to the
    ///        Foundry project root (for example
    ///        `../Challenge/Ripemd160/Reference`).
    function load(Vm vm, string memory referenceDir) internal view returns (Pin memory pin) {
        bytes memory fromHex = parseHex(vm.readFile(string.concat(referenceDir, "/reference.hex")));

        string memory bytesLean = vm.readFile(string.concat(referenceDir, "/Bytes.lean"));
        (bytes memory fromLiteral, uint256 chunkCount) = parseLeanLiteral(bytesLean);

        require(keccak256(fromHex) == keccak256(fromLiteral), "LeanArtifact: hex file != Lean literal");

        string memory bytecodeLean = vm.readFile(string.concat(referenceDir, "/Bytecode.lean"));
        require(
            contains(bytecodeLean, 'include_str "reference.hex"'),
            "LeanArtifact: Bytecode.lean no longer includes reference.hex"
        );
        require(
            contains(bytecodeLean, "referenceBytecode : ByteArray := referenceBytes"),
            "LeanArtifact: referenceBytecode is no longer referenceBytes"
        );

        uint256 literalSize = parseProvedSize(bytesLean, "referenceBytes.size = ");
        uint256 bytecodeSize = parseProvedSize(bytecodeLean, "referenceBytecode.size = ");
        require(literalSize == fromHex.length, "LeanArtifact: referenceBytes_size disagrees");
        require(bytecodeSize == fromHex.length, "LeanArtifact: referenceBytecode_size disagrees");

        pin.code = fromHex;
        pin.chunkCount = chunkCount;
        pin.provedSize = bytecodeSize;
    }

    // ── reference.hex ───────────────────────────────────────────────

    /// @notice Parses a hex artifact, tolerating surrounding whitespace and an
    ///         optional `0x` prefix but rejecting any other character.
    function parseHex(string memory text) internal pure returns (bytes memory out) {
        bytes memory t = bytes(text);
        uint256 i = 0;
        while (i < t.length && isSpace(t[i])) i++;
        if (i + 1 < t.length && t[i] == "0" && (t[i + 1] == "x" || t[i + 1] == "X")) i += 2;

        bytes memory buffer = new bytes(t.length / 2 + 1);
        uint256 n = 0;
        uint256 high = 0;
        bool haveHigh = false;
        for (; i < t.length; i++) {
            if (isSpace(t[i])) continue;
            uint256 v = hexValue(t[i]);
            if (!haveHigh) {
                high = v;
                haveHigh = true;
            } else {
                buffer[n++] = bytes1(uint8(high * 16 + v));
                haveHigh = false;
            }
        }
        require(!haveHigh, "LeanArtifact: odd number of hex digits");
        out = truncate(buffer, n);
    }

    // ── Bytes.lean ──────────────────────────────────────────────────

    /// @notice Parses `Bytes.lean` into the bytes `referenceBytes` denotes.
    /// @dev Chunk literals are read in source order; the returned bytes follow
    ///      the order in which the `referenceBytes` body concatenates them,
    ///      which is what the proof actually reasons about.
    function parseLeanLiteral(string memory text)
        internal
        pure
        returns (bytes memory out, uint256 chunkCount)
    {
        bytes memory t = bytes(text);

        // Chunk index -> byte payload. Indices are small and dense; the bound
        // is a sanity limit, not a property of any particular artifact.
        bytes[] memory chunks = new bytes[](1024);

        uint256 cursor = 0;
        while (true) {
            (bool found, uint256 pos) = indexOf(t, CHUNK_DECL, cursor);
            if (!found) break;
            (uint256 index, uint256 afterIndex) = parseUint(t, pos + bytes(CHUNK_DECL).length);
            require(index < 1024, "LeanArtifact: chunk index out of range");

            (bool openFound, uint256 open) = indexOf(t, LITERAL_OPEN, afterIndex);
            require(openFound, "LeanArtifact: chunk literal has no ByteArray.mk");
            uint256 payload = open + bytes(LITERAL_OPEN).length;
            (bool closeFound, uint256 close) = indexOf(t, "]", payload);
            require(closeFound, "LeanArtifact: chunk literal is unterminated");

            require(chunks[index].length == 0, "LeanArtifact: duplicate chunk index");
            chunks[index] = parseByteTokens(t, payload, close);
            require(chunks[index].length > 0, "LeanArtifact: empty chunk literal");
            chunkCount++;
            cursor = close + 1;
        }
        require(chunkCount > 0, "LeanArtifact: no chunk literals found");

        out = concatInBodyOrder(t, chunks, chunkCount);
    }

    /// @dev Concatenates chunks in the order the `referenceBytes` body lists
    ///      them, requiring every parsed chunk to be used exactly once.
    function concatInBodyOrder(bytes memory t, bytes[] memory chunks, uint256 chunkCount)
        private
        pure
        returns (bytes memory out)
    {
        (bool defFound, uint256 defAt) = indexOf(t, BYTES_DECL, 0);
        require(defFound, "LeanArtifact: referenceBytes definition not found");
        uint256 bodyStart = defAt + bytes(BYTES_DECL).length;
        (bool endFound, uint256 bodyEnd) = indexOf(t, "@[simp]", bodyStart);
        if (!endFound) bodyEnd = t.length;

        uint256 total = 0;
        for (uint256 i = 0; i < chunks.length; i++) {
            total += chunks[i].length;
        }
        bytes memory buffer = new bytes(total);

        bool[] memory used = new bool[](chunks.length);
        uint256 written = 0;
        uint256 usedCount = 0;
        uint256 cursor = bodyStart;
        while (true) {
            (bool found, uint256 pos) = indexOf(t, CHUNK_REF, cursor);
            if (!found || pos >= bodyEnd) break;
            (uint256 index, uint256 afterIndex) = parseUint(t, pos + bytes(CHUNK_REF).length);
            require(index < chunks.length && chunks[index].length > 0, "LeanArtifact: unknown chunk in body");
            require(!used[index], "LeanArtifact: chunk concatenated twice");
            used[index] = true;
            usedCount++;

            bytes memory chunk = chunks[index];
            for (uint256 i = 0; i < chunk.length; i++) {
                buffer[written + i] = chunk[i];
            }
            written += chunk.length;
            cursor = afterIndex;
        }
        require(usedCount == chunkCount, "LeanArtifact: body omits a chunk literal");
        out = truncate(buffer, written);
    }

    /// @dev Reads `0x`-prefixed byte tokens from `t[start..end)`, rejecting any
    ///      character that is not part of a token, a comma, or whitespace.
    function parseByteTokens(bytes memory t, uint256 start, uint256 end)
        private
        pure
        returns (bytes memory out)
    {
        bytes memory buffer = new bytes((end - start) / 4 + 1);
        uint256 n = 0;
        uint256 i = start;
        while (i < end) {
            if (isSpace(t[i]) || t[i] == ",") {
                i++;
                continue;
            }
            require(i + 3 < end && t[i] == "0" && t[i + 1] == "x", "LeanArtifact: malformed byte token");
            buffer[n++] = bytes1(uint8(hexValue(t[i + 2]) * 16 + hexValue(t[i + 3])));
            i += 4;
        }
        out = truncate(buffer, n);
    }

    /// @notice Parses the decimal literal that follows `marker`, used to read
    ///         the size a Lean theorem proves.
    function parseProvedSize(string memory text, string memory marker) internal pure returns (uint256) {
        bytes memory t = bytes(text);
        (bool found, uint256 pos) = indexOf(t, marker, 0);
        require(found, "LeanArtifact: size theorem not found");
        (uint256 value,) = parseUint(t, pos + bytes(marker).length);
        return value;
    }

    // ── small string utilities ──────────────────────────────────────

    function contains(string memory haystack, string memory needle) internal pure returns (bool found) {
        (found,) = indexOf(bytes(haystack), needle, 0);
    }

    function indexOf(bytes memory haystack, string memory needle, uint256 from)
        internal
        pure
        returns (bool, uint256)
    {
        bytes memory n = bytes(needle);
        if (n.length == 0 || haystack.length < n.length) return (false, 0);
        for (uint256 i = from; i + n.length <= haystack.length; i++) {
            bool hit = true;
            for (uint256 j = 0; j < n.length; j++) {
                if (haystack[i + j] != n[j]) {
                    hit = false;
                    break;
                }
            }
            if (hit) return (true, i);
        }
        return (false, 0);
    }

    function parseUint(bytes memory t, uint256 pos) private pure returns (uint256 value, uint256 next) {
        uint256 digits = 0;
        while (pos < t.length && t[pos] >= "0" && t[pos] <= "9") {
            value = value * 10 + (uint8(t[pos]) - 48);
            pos++;
            digits++;
        }
        require(digits > 0, "LeanArtifact: expected a number");
        next = pos;
    }

    function hexValue(bytes1 c) private pure returns (uint256) {
        if (c >= "0" && c <= "9") return uint8(c) - 48;
        if (c >= "a" && c <= "f") return uint8(c) - 87;
        if (c >= "A" && c <= "F") return uint8(c) - 55;
        revert("LeanArtifact: not a hex digit");
    }

    function isSpace(bytes1 c) private pure returns (bool) {
        return c == 0x20 || c == 0x0a || c == 0x0d || c == 0x09;
    }

    function truncate(bytes memory buffer, uint256 n) private pure returns (bytes memory out) {
        out = buffer;
        assembly {
            mstore(out, n)
        }
    }
}
