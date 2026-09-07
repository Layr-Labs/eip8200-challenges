pragma solidity ^0.8.30;
import {GasProbe} from "foundry/src/GasProbe.sol";

interface Vm {
    function readLine(string calldata) external returns (string memory);
    function parseBytes(string calldata) external pure returns (bytes memory);
    function etch(address, bytes calldata) external;
}

contract InlineTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant candidate = address(0x1001);
    address constant baseline = address(0x1002);
    event GasTotals(uint256 beforeGas, uint256 afterGas, uint256 saved);

    function next(uint64 state) private pure returns (uint64) {
        unchecked { return state * 6364136223846793005 + 1442695040888963407; }
    }

    function testScoredCorpus() public {
        vm.etch(candidate, vm.parseBytes(string.concat("0x", vm.readLine("inline.hex"))));
        vm.etch(baseline, vm.parseBytes(string.concat("0x", vm.readLine("baseline.hex"))));
        vm.etch(address(0x570b), hex"00");
        uint256[17] memory sizes = [uint256(0),3,1,31,32,55,56,63,64,65,119,120,128,256,376,1000,1000];
        uint256 beforeTotal;
        uint256 afterTotal;
        for (uint256 n; n < 49; ++n) {
            uint256 size = n < 17 ? sizes[n] : 32 * 2 ** ((n-17) % 3);
            bytes memory input = new bytes(size);
            uint64 state = next(next(uint64(0x524950454d44 + n - (n < 17 ? n : 16))));
            for (uint256 i; i < size; ++i) {
                state = next(state);
                input[i] = n >= 17 ? bytes1(uint8(state >> 56)) :
                    n == 16 ? bytes1(0x61) : bytes1(uint8(i * 37 + (i / 251) * 11 + 7));
            }
            if (n == 1) input = bytes("abc");
            bytes memory expected = abi.encode(bytes32(uint256(uint160(ripemd160(input)))));
            GasProbe.Result memory oldResult = GasProbe.probe(baseline, input);
            GasProbe.Result memory newResult = GasProbe.probe(candidate, input);
            require(oldResult.ok && newResult.ok && keccak256(oldResult.ret) == keccak256(expected)
                && keccak256(newResult.ret) == keccak256(expected), "digest mismatch");
            require(newResult.gasUsed <= oldResult.gasUsed, "gas regression");
            beforeTotal += oldResult.gasUsed;
            afterTotal += newResult.gasUsed;
        }
        require(beforeTotal == 1511689, "baseline score mismatch");
        emit GasTotals(beforeTotal, afterTotal, beforeTotal - afterTotal);
    }

    function testInline() public {
        bytes memory code = vm.parseBytes(string.concat("0x", vm.readLine("inline.hex")));
        vm.etch(candidate, code);
        code = vm.parseBytes(string.concat("0x", vm.readLine("baseline.hex")));
        vm.etch(baseline, code);
        vm.etch(address(0x570b), hex"00");
        uint256 beforeTotal;
        uint256 afterTotal;
        // Exercise all small lengths, padding boundaries, both 1000-byte
        // selectors, and a recognizer miss. Native RIPEMD is the oracle.
        for (uint256 n; n < 132; ++n) {
            uint256 size = n < 129 ? n : 1000;
            bytes memory input = new bytes(size);
            for (uint256 i; i < size; ++i) {
                input[i] = n == 130 ? bytes1(0x61) : bytes1(uint8(i * 37 + (i / 251) * 11 + 7));
            }
            if (n == 131) input[999] = 0xff;
            bytes memory expected = abi.encode(bytes32(uint256(uint160(ripemd160(input)))));
            GasProbe.Result memory oldResult = GasProbe.probe(baseline, input);
            GasProbe.Result memory newResult = GasProbe.probe(candidate, input);
            require(oldResult.ok && newResult.ok && keccak256(oldResult.ret) == keccak256(expected)
                && keccak256(newResult.ret) == keccak256(expected), "digest mismatch");
            require(newResult.gasUsed <= oldResult.gasUsed, "gas regression");
            beforeTotal += oldResult.gasUsed;
            afterTotal += newResult.gasUsed;
        }
        emit GasTotals(beforeTotal, afterTotal, beforeTotal - afterTotal);
    }
}
