pragma solidity ^0.8.0;

contract TimeLottery {
    address public winner;

    function pickWinner() public {
        require(block.timestamp % 2 == 0, "Not an even timestamp");
        winner = msg.sender;
    }
}
