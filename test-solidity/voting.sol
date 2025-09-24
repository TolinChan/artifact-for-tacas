
contract Voting {

          // State variables managed by TransitionSystem
    uint256 public now;
    string public func;

    uint256 public currentState;


    constructor() {
        currentState = 0;
    }

        
    function vote() public {
                require(true, "Transition not allowed");

        currentState = 0;
    }

        }