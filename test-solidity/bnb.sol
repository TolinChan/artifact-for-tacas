
contract Bnb {

          // State variables managed by TransitionSystem
    uint256 public now;
    string public func;

    uint256 public currentState;


    constructor() {
        currentState = 0;
    }

        
    function transfer() public {
                require(true, "Transition not allowed");

        currentState = 0;
    }

        
    function approve() public {
                require(true, "Transition not allowed");

        currentState = 1;
    }

        
    function transferFrom() public {
                require(true, "Transition not allowed");

        currentState = 2;
    }

        
    function burn() public {
                require(true, "Transition not allowed");

        currentState = 3;
    }

        
    function freeze() public {
                require(true, "Transition not allowed");

        currentState = 4;
    }

        
    function unfreeze() public {
                require(true, "Transition not allowed");

        currentState = 5;
    }

        }