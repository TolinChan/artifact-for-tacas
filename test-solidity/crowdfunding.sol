contract Crowfunding {
  struct TargetTuple {
    uint t;
    bool _valid;
  }
  struct RaisedTuple {
    uint n;
    bool _valid;
  }
  struct ClosedTuple {
    bool b;
    bool _valid;
  }
  struct BeneficiaryTuple {
    address p;
    bool _valid;
  }
  struct OwnerTuple {
    address p;
    bool _valid;
  }
  struct BalanceOfTuple {
    uint n;
    bool _valid;
  }
  TargetTuple target;
  RaisedTuple raised;
  ClosedTuple closed;
  BeneficiaryTuple beneficiary;
  mapping(address=>BalanceOfTuple) balanceOf;
  OwnerTuple owner;
  event Refund(address p,uint n);
  event Invest(address p,uint n);
  event Closed(bool b);
  event Withdraw(address p,uint n);
  constructor(uint t,address b) public {
    updateBeneficiaryOnInsertConstructor_r12(b);
    updateTargetOnInsertConstructor_r0(t);
    updateRaisedOnInsertConstructor_r6();
    updateOwnerOnInsertConstructor_r7();
  }
  function getClosed() public view  returns (bool) {
      bool b = closed.b;
      return b;
  }
  function getRaised() public view  returns (uint) {
      uint n = raised.n;
      return n;
  }
  function refund() public    {
      require((!(closed.b)),"Synthesis guard failed");
      bool r2 = updateRefundOnInsertRecv_refund_r2();
      if(r2==false) {
        revert("Rule condition failed");
      }
  }
  function close() public    {
      bool r9 = updateClosedOnInsertRecv_close_r9();
      if(r9==false) {
        revert("Rule condition failed");
      }
  }
  function invest() public  payable  {
      bool r4 = updateInvestOnInsertRecv_invest_r4();
      if(r4==false) {
        revert("Rule condition failed");
      }
  }
  function withdraw() public    {
      bool r8 = updateWithdrawOnInsertRecv_withdraw_r8();
      if(r8==false) {
        revert("Rule condition failed");
      }
  }
  function updateInvestOnInsertRecv_invest_r4() private   returns (bool) {
      if(false==closed.b) {
        uint s = raised.n;
        uint t = target.t;
        uint n = msg.value;
        address p = msg.sender;
        if(s<t) {
          updateInvestTotalOnInsertInvest_r5(p,n);
          updateRaisedOnInsertInvest_r10(n);
          emit Invest(p,n);
          return true;
        }
      }
      return false;
  }
  function updateWithdrawOnInsertRecv_withdraw_r8() private   returns (bool) {
      address p = beneficiary.p;
      uint t = target.t;
      uint r = raised.n;
      if(p==msg.sender) {
        if(r>=t) {
          emit Withdraw(p,r);
          return true;
        }
      }
      return false;
  }
  function updateRefundTotalOnInsertRefund_r11(address p,uint m) private    {
      int delta0 = int(m);
      updateBalanceOfOnIncrementRefundTotal_r1(p,delta0);
  }
  function updateuintByint(uint x,int delta) private   returns (uint) {
      int convertedX = int(x);
      int value = convertedX+delta;
      uint convertedValue = uint(value);
      return convertedValue;
  }
  function updateInvestTotalOnInsertInvest_r5(address p,uint m) private    {
      int delta0 = int(m);
      updateBalanceOfOnIncrementInvestTotal_r1(p,delta0);
  }
  function updateRaisedOnInsertConstructor_r6() private    {
      raised = RaisedTuple(0,true);
  }
  function updateBalanceOfOnIncrementRefundTotal_r1(address p,int r) private    {
      int _delta = int(-r);
      uint newValue = updateuintByint(balanceOf[p].n,_delta);
      balanceOf[p].n = newValue;
  }
  function updateBalanceOfOnIncrementInvestTotal_r1(address p,int i) private    {
      int _delta = int(i);
      uint newValue = updateuintByint(balanceOf[p].n,_delta);
      balanceOf[p].n = newValue;
  }
  function updateBeneficiaryOnInsertConstructor_r12(address p) private    {
      beneficiary = BeneficiaryTuple(p,true);
  }
  function updateRefundOnInsertRecv_refund_r2() private   returns (bool) {
      if(true==closed.b) {
        address p = msg.sender;
        uint t = target.t;
        uint r = raised.n;
        uint n = balanceOf[p].n;
        if(r<t && n>0) {
          updateRefundTotalOnInsertRefund_r11(p,n);
          emit Refund(p,n);
          return true;
        }
      }
      return false;
  }
  function updateOwnerOnInsertConstructor_r7() private    {
      address p = msg.sender;
      owner = OwnerTuple(p,true);
  }
  function updateTargetOnInsertConstructor_r0(uint t) private    {
      target = TargetTuple(t,true);
  }
  function updateRaisedOnInsertInvest_r10(uint m) private    {
      raised.n += m;
  }
  function updateClosedOnInsertRecv_close_r9() private   returns (bool) {
      address s = owner.p;
      if(s==msg.sender) {
        closed = ClosedTuple(true,true);
        emit Closed(true);
        return true;
      }
      return false;
  }
}