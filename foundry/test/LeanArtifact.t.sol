// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {Vm} from "forge-std/Vm.sol";
import {LeanArtifact} from "../src/LeanArtifact.sol";

/// @dev Exposes the library across a call boundary so a failed load can be
///      caught and its reason inspected.
contract ArtifactLoader {
    function load(Vm vm, string memory referenceDir) external view returns (bytes memory) {
        return LeanArtifact.load(vm, referenceDir).code;
    }
}

/// @notice Negative controls for the artifact provenance check.
///
/// @dev The gas cross-check is only as good as its claim to be measuring the
///      bytecode the Lean proofs cover, and that claim rests entirely on
///      `LeanArtifact.load`. A provenance check that cannot fail would be worse
///      than none at all, so each way the artifacts could drift apart is
///      reproduced here against corrupted copies and required to be rejected.
contract LeanArtifactTest is Test {
    ArtifactLoader internal loader;

    string internal constant SOURCE_DIR = "../Challenge/Ripemd160/Reference";
    string internal constant WORK_DIR = "cache/artifact-selftest";

    function setUp() public {
        loader = new ArtifactLoader();
    }

    /// @dev Copies the three artifacts into a scratch directory so a corrupted
    ///      variant can be written without touching the challenge.
    /// @dev `name` keeps each test in its own directory: Foundry runs test
    ///      functions concurrently, and filesystem writes are not rolled back
    ///      between them, so a shared scratch directory would race.
    function _stage(string memory name) internal returns (string memory dir) {
        dir = string.concat(WORK_DIR, "/", name);
        vm.createDir(dir, true);
        _copy("reference.hex", dir);
        _copy("Bytes.lean", dir);
        _copy("Bytecode.lean", dir);
    }

    function _copy(string memory name, string memory dir) private {
        vm.writeFile(string.concat(dir, "/", name), vm.readFile(string.concat(SOURCE_DIR, "/", name)));
    }

    function _expectRejection(string memory dir, string memory expectedReason) private {
        try loader.load(vm, dir) {
            fail(string.concat("load accepted a corrupted artifact: ", expectedReason));
        } catch Error(string memory reason) {
            assertEq(reason, expectedReason, "rejection reason");
        }
    }

    /// @dev The control on the controls: an untouched copy must load, otherwise
    ///      the rejections below would prove nothing.
    function test_pristine_copy_loads() public {
        string memory dir = _stage("pristine");
        bytes memory staged = loader.load(vm, dir);
        bytes memory original = loader.load(vm, SOURCE_DIR);
        assertEq(staged, original, "staged copy differs from the challenge artifact");
        assertEq(staged.length, 1671, "reference size");
    }

    /// @dev A hex file that no longer matches the literal the proof is about is
    ///      the central failure this check exists to catch.
    function test_rejects_hex_that_diverges_from_the_lean_literal() public {
        string memory dir = _stage("hex-diverges");
        string memory hexText = vm.readFile(string.concat(dir, "/reference.hex"));
        bytes memory raw = bytes(hexText);
        // Flip one nibble: same length, different bytecode.
        raw[10] = raw[10] == "0" ? bytes1("1") : bytes1("0");
        vm.writeFile(string.concat(dir, "/reference.hex"), string(raw));

        _expectRejection(dir, "LeanArtifact: hex file != Lean literal");
    }

    /// @dev Truncating the literal changes the bytes and the length; the byte
    ///      comparison must catch it before the size theorems do.
    function test_rejects_truncated_lean_literal() public {
        string memory dir = _stage("truncated-literal");
        string memory text = vm.readFile(string.concat(dir, "/Bytes.lean"));
        vm.writeFile(string.concat(dir, "/Bytes.lean"), _dropLastChunkReference(text));

        _expectRejection(dir, "LeanArtifact: body omits a chunk literal");
    }

    /// @dev If `referenceBytecode` stops being `referenceBytes`, then
    ///      `Correct referenceBytecode` is no longer a statement about these
    ///      bytes, however well the hex file matches the literal.
    function test_rejects_bytecode_decoupled_from_the_literal() public {
        string memory dir = _stage("decoupled");
        string memory text = vm.readFile(string.concat(dir, "/Bytecode.lean"));
        vm.writeFile(
            string.concat(dir, "/Bytecode.lean"),
            _replace(
                text,
                "referenceBytecode : ByteArray := referenceBytes",
                "referenceBytecode : ByteArray := somethingElse"
            )
        );

        _expectRejection(dir, "LeanArtifact: referenceBytecode is no longer referenceBytes");
    }

    /// @dev The size the Lean theorem proves has to be the size of the bytes
    ///      actually executed.
    function test_rejects_disagreeing_size_theorem() public {
        string memory dir = _stage("size-theorem");
        string memory text = vm.readFile(string.concat(dir, "/Bytecode.lean"));
        vm.writeFile(
            string.concat(dir, "/Bytecode.lean"),
            _replace(text, "referenceBytecode.size = 1671", "referenceBytecode.size = 1672")
        );

        _expectRejection(dir, "LeanArtifact: referenceBytecode_size disagrees");
    }

    /// @dev A `Bytecode.lean` that no longer includes the hex file leaves the
    ///      two artifacts free to drift apart in future edits.
    function test_rejects_missing_include_str() public {
        string memory dir = _stage("missing-include");
        string memory text = vm.readFile(string.concat(dir, "/Bytecode.lean"));
        vm.writeFile(
            string.concat(dir, "/Bytecode.lean"),
            _replace(text, 'include_str "reference.hex"', 'include_str "elsewhere.hex"')
        );

        _expectRejection(dir, "LeanArtifact: Bytecode.lean no longer includes reference.hex");
    }

    // ── text helpers ────────────────────────────────────────────────

    /// @dev Removes the final ` ++ referenceChunk<N>` from the `referenceBytes`
    ///      body, leaving a literal that no longer covers the whole artifact.
    function _dropLastChunkReference(string memory text) private pure returns (string memory) {
        bytes memory t = bytes(text);
        (bool found, uint256 defAt) = LeanArtifact.indexOf(t, "abbrev referenceBytes : ByteArray :=", 0);
        require(found, "selftest: definition not found");
        (bool endFound, uint256 bodyEnd) = LeanArtifact.indexOf(t, "@[simp]", defAt);
        require(endFound, "selftest: body end not found");

        // Walk back to the last "++" inside the body and cut from there.
        uint256 cut = bodyEnd;
        while (cut > defAt) {
            cut--;
            if (t[cut] == "+" && t[cut - 1] == "+") {
                cut -= 1;
                break;
            }
        }
        bytes memory out = new bytes(t.length - (bodyEnd - cut));
        for (uint256 i = 0; i < cut; i++) {
            out[i] = t[i];
        }
        for (uint256 i = bodyEnd; i < t.length; i++) {
            out[cut + (i - bodyEnd)] = t[i];
        }
        return string(out);
    }

    /// @dev Replaces the first occurrence of `needle` with `replacement`.
    function _replace(string memory text, string memory needle, string memory replacement)
        private
        pure
        returns (string memory)
    {
        bytes memory t = bytes(text);
        (bool found, uint256 at) = LeanArtifact.indexOf(t, needle, 0);
        require(found, "selftest: needle not found");
        bytes memory n = bytes(needle);
        bytes memory r = bytes(replacement);

        bytes memory out = new bytes(t.length - n.length + r.length);
        for (uint256 i = 0; i < at; i++) {
            out[i] = t[i];
        }
        for (uint256 i = 0; i < r.length; i++) {
            out[at + i] = r[i];
        }
        for (uint256 i = at + n.length; i < t.length; i++) {
            out[i - n.length + r.length] = t[i];
        }
        return string(out);
    }
}
