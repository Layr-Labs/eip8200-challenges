// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {GasCrossCheck} from "./GasCrossCheck.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {Vectors} from "../src/Vectors.sol";

/// @notice Validates the measurement method itself.
///
/// @dev Every gas number this suite reports is `GasProbe.probe` output, so the
///      probe has to be checked against quantities that are known exactly and
///      independently. The `0x02` and `0x03` precompiles have closed-form gas
///      schedules fixed by protocol, which makes them the ideal control: if the
///      probe over- or under-counted by even one gas — a mispriced call
///      instruction, an unwarmed account, a memory expansion leaking into the
///      window — these assertions fail.
///
///      The remaining tests measure the same way, so passing here is what
///      licenses reading their numbers as frame gas.
contract GasProbeTest is GasCrossCheck {
    /// @dev `600 + 120 * ceil(len / 32)`, the RIPEMD-160 precompile schedule.
    function _ripemdPrecompileGas(uint256 len) private pure returns (uint256) {
        return 600 + 120 * ((len + 31) / 32);
    }

    /// @dev `60 + 12 * ceil(len / 32)`, the SHA-256 precompile schedule.
    function _sha256PrecompileGas(uint256 len) private pure returns (uint256) {
        return 60 + 12 * ((len + 31) / 32);
    }

    function test_probe_matches_ripemd160_precompile_schedule() public view {
        uint256[7] memory sizes = [uint256(0), 1, 31, 32, 33, 376, 1000];
        for (uint256 i = 0; i < sizes.length; i++) {
            bytes memory input = Vectors.patterned(sizes[i]);
            (uint256 gasUsed,) = _gas(address(0x03), input);
            assertEq(gasUsed, _ripemdPrecompileGas(sizes[i]), "ripemd160 precompile gas");
        }
    }

    function test_probe_matches_sha256_precompile_schedule() public view {
        uint256[7] memory sizes = [uint256(0), 1, 31, 32, 33, 376, 1000];
        for (uint256 i = 0; i < sizes.length; i++) {
            bytes memory input = Vectors.patterned(sizes[i]);
            (uint256 gasUsed,) = _gas(address(0x02), input);
            assertEq(gasUsed, _sha256PrecompileGas(sizes[i]), "sha256 precompile gas");
        }
    }

    /// @dev A frame holding a single `STOP` consumes nothing, so the probe must
    ///      report exactly zero once its overhead is removed.
    function test_probe_reports_zero_for_empty_frame() public {
        address stopper = address(uint160(0x9001));
        vm.etch(stopper, hex"00");
        (uint256 gasUsed,) = _gas(stopper, Vectors.patterned(64));
        assertEq(gasUsed, 0, "STOP frame gas");
    }

    /// @dev The result must not depend on how much the caller has already
    ///      touched: the probe warms the target and pre-expands memory itself.
    function test_probe_is_independent_of_caller_state() public view {
        bytes memory input = Vectors.patterned(1000);
        (uint256 cold,) = _gas(address(0x03), input);

        // Touch the target and grow caller memory, then measure again.
        (bool ok,) = address(0x03).staticcall(input);
        require(ok, "precompile call failed");
        bytes memory ballast = new bytes(200_000);
        ballast[199_999] = 0x01;

        (uint256 warm,) = _gas(address(0x03), input);
        assertEq(warm, cold, "measurement depends on caller state");
    }

    /// @dev Two sizes that differ by one 32-byte word must differ by exactly one
    ///      word of precompile cost, which pins the probe's scaling rather than
    ///      just its offset.
    function test_probe_scales_with_input_size() public view {
        (uint256 g32,) = _gas(address(0x03), Vectors.patterned(32));
        (uint256 g33,) = _gas(address(0x03), Vectors.patterned(33));
        assertEq(g33 - g32, 120, "one extra ripemd160 word");
    }

    /// @dev The calibration target must be the zero-gas frame the probe assumes.
    function test_calibration_target_is_stop() public view {
        assertEq(GasProbe.STOP_TARGET.code, hex"00", "calibration target code");
    }
}
