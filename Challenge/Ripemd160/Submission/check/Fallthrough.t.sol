pragma solidity ^0.8.30;
import {GasProbe} from "../../../../foundry/src/GasProbe.sol";

interface Vm {
    function readLine(string calldata) external returns (string memory);
    function parseBytes(string calldata) external pure returns (bytes memory);
    function etch(address, bytes calldata) external;
}

contract FallthroughTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant candidate = address(0x1001);
    address constant baseline = address(0x1002);
    event GasTotals(uint256 beforeGas, uint256 afterGas, uint256 saved);

    function testFallthrough() public {
        bytes memory code = vm.parseBytes(string.concat("0x", vm.readLine("../bytecode.hex")));
        require(code.length == 5268 && code[4967] == 0x50);
        vm.etch(candidate, code);
        code[4967] = 0x56;
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
            require(oldResult.gasUsed - newResult.gasUsed == (n == 129 || n == 131 ? 6 : 0),
                "unexpected gas delta");
            beforeTotal += oldResult.gasUsed;
            afterTotal += newResult.gasUsed;
        }
        emit GasTotals(beforeTotal, afterTotal, beforeTotal - afterTotal);
    }
}
