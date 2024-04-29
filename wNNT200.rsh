"reach 0.1";

const MAX_DECIMALS = 256; // decimals fits in UInt8

const TokenMeta = Struct([
  ["name", Bytes(32)], // name
  ["symbol", Bytes(8)], // symbol
  ["decimals", UInt], // number of decimals
  ["totalSupply", UInt256], // total supply
]);

const MintParams = Object({
  name: Bytes(32), // name
  symbol: Bytes(8), // symbol
  decimals: UInt, // number of decimals
});

const NNT200 = () =>
  Reach.App(() => {
    setOptions({ connectors: [ALGO] });

    const State = Struct([
      ...Struct.fields(TokenMeta),
      ["zeroAddress", Address],
      ["manager", Address],
      ["closed", Bool],
      ["token", Token],
      ["tokenAmount", UInt],
    ]);

    const Params = Object({
      zeroAddress: Address, // zero address
      meta: MintParams, // token meta
      tok: Token,
    });

    const D = Participant("Deployer", {
      params: Params, // deployer params
      ready: Fun([Contract], Null), // token ready
    });

    const A = API({
      arc200_transfer: Fun([Address, UInt256], Bool), // tranfer from this to address
      arc200_transferFrom: Fun([Address, Address, UInt256], Bool), // transfer from address to address
      arc200_approve: Fun([Address, UInt256], Bool), // approve address to spend this
      deleteBalanceBox: Fun([Address], Bool), // delete balance box if zero
      deleteAllowanceBox: Fun([Address, Address], Bool), // delete allowance box if zero
      destroy: Fun([], Null), // destroy this contract
      deposit: Fun([UInt], UInt256),
      withdraw: Fun([UInt], UInt256),
    });

    const V = View({
      name: Fun([], Bytes(32)), // get name
      symbol: Fun([], Bytes(8)), // get symbol
      decimals: Fun([], UInt), // get decimals
      totalSupply: Fun([], UInt256), // get total supply
      balanceOf: Fun([Address], UInt256), // get balance of address
      allowance: Fun([Address, Address], UInt256), // get allowance of address to spend this
      state: Fun([], State), // get state
    });

    const N = Events({
      Transfer: [Address, Address, UInt256],
      Approval: [Address, Address, UInt256],
    });

    init();

    D.only(() => {
      const { zeroAddress, meta, tok } = declassify(interact.params);
    });
    D.publish(zeroAddress, meta, tok).check(() => {
      check(
        meta.decimals <= MAX_DECIMALS,
        "ARC200: Decimals must be less than 19"
      );
    });

    const balances = new Map(UInt256);
    const allowances = new Map(Tuple(Address, Address), UInt256);

    const manager = getAddress();

    balances[manager] = UInt256.max;
    balances[zeroAddress] = UInt256(0);

    N.arc200_Transfer(zeroAddress, getAddress(), UInt256.max);
    D.interact.ready(getContract());

    V.name.set(() => meta.name);
    V.symbol.set(() => meta.symbol);
    V.decimals.set(() => meta.decimals);
    V.totalSupply.set(() => UInt256.max);

    const initialState = {
      ...meta,
      totalSupply: UInt256.max,
      zeroAddress,
      manager,
      closed: false,
      token: tok,
      tokenAmount: 0,
    };

    const [s] = parallelReduce([initialState])
      .define(() => {
        const state = () => State.fromObject(s);
        V.state.set(state);
        const balanceOf_ = (owner) => {
          const m_bal = balances[owner];
          return fromSome(m_bal, UInt256(0));
        };
        const allowance_ = (owner, spender) => {
          const m_bal = allowances[[owner, spender]];
          return fromSome(m_bal, UInt256(0));
        };
        const transfer_ = (from_, to, amount) => {
          balances[from_] = balanceOf_(from_) - amount;
          balances[to] = balanceOf_(to) + amount;
          N.arc200_Transfer(from_, to, amount);
        };
        const transferFrom_ = (spender, from_, to, value) => {
          transfer_(from_, to, value);
          const newAllowance = allowance_(from_, spender) - value;
          allowances[[from_, spender]] = newAllowance;
          N.arc200_Approval(from_, spender, newAllowance);
        };
        const arc200 = {
          balanceOf: balanceOf_,
          allowance: allowance_,
          transfer: transfer_,
          transferFrom: transferFrom_,
        };
        V.balanceOf.set(arc200.balanceOf);
        V.allowance.set(arc200.allowance);
      })
      .invariant(balance() == 0)
      .invariant(implies(!s.closed, balance(tok) == s.tokenAmount))
      .invariant(implies(s.closed, balance(tok) == 0))
      .while(!s.closed)
      .paySpec([tok])
      // api: transfer
      // - transfer from this to address
      // + may transfer to zero address (burn) if zero address burn enabled
      .api_(ARC200.transfer, (to, amount) => {
        check(to != zeroAddress, "ARC200: Transfer to zero address");
        check(
          arc200.balanceOf(this) >= amount,
          "ARC200: Transfer amount must not be greater than balance"
        );
        return [
          (k) => {
            arc200.transfer(this, to, amount);
            k(true);
            return [s];
          },
        ];
      })
      // api: transferFrom
      // - transfer from address to address
      // + may not transfer to and from zero address
      // + requires allowance from spender to this
      .api_(ARC200.transferFrom, (from_, to, amount) => {
        check(from_ != zeroAddress, "ARC200: Transfer from zero address");
        check(to != zeroAddress, "ARC200: Transfer to zero address");
        check(
          arc200.balanceOf(from_) >= amount,
          "ARC200: Amount must not be greater than balance"
        );
        check(
          arc200.allowance(from_, this) >= amount,
          "ARC200: Amount must not be greater than allowance"
        );
        return [
          (k) => {
            arc200.transferFrom(this, from_, to, amount);
            k(true);
            return [s];
          },
        ];
      })
      // api: approve
      // - approve address to spend this
      // + may not approve zero address
      // + may not approve this if zero address
      .api_(ARC200.approve, (spender, amount) => {
        check(this != zeroAddress, "ARC200: Approve this to zero address");
        check(spender != zeroAddress, "ARC200: Approve to zero address");
        return [
          (k) => {
            allowances[[this, spender]] = amount;
            N.arc200_Approval(this, spender, amount);
            k(true);
            return [s];
          },
        ];
      })
      .api_(A.deposit, (amt) => {
        return [
          [0, [amt, tok]],
          (k) => {
            arc200.transfer(getAddress(), this, UInt256(amt));
            k(arc200.balanceOf(this) + UInt256(amt));
            return [
              {
                ...s,
                tokenAmount: s.tokenAmount + amt,
              },
            ];
          },
        ];
      })
      .api_(A.withdraw, (amt) => {
        check(
          arc200.balanceOf(this) >= UInt256(amt),
          "Withdraw: insufficient balance"
        );
        // approval check here
        check(s.tokenAmount >= amt);
        return [
          (k) => {
            arc200.transferFrom(getAddress(), this, getAddress(), UInt256(amt));
            transfer([[amt, tok]]).to(this);
            k(arc200.balanceOf(this) - UInt256(amt));
            return [
              {
                ...s,
                tokenAmount: s.tokenAmount - amt,
              },
            ];
          },
        ];
      })
      // api: deleteBalanceBox
      // - delete balance box if zero
      // + requires address not zero address
      // + requires balance box to exist
      // + requires balance box to be zero or zero address balance box to be total supply
      .api_(A.deleteBalanceBox, (addr) => {
        check(
          addr != zeroAddress,
          "ARC200: Delete balance box to zero address"
        );
        check(isSome(balances[addr]), "ARC200: Balance box not found");
        check(
          arc200.balanceOf(addr) == UInt256(0),
          "ARC200: Balance box not empty"
        );
        return [
          (k) => {
            delete balances[addr];
            k(true);
            return [s];
          },
        ];
      })
      // api: deleteAllowanceBox
      // - delete allowance box if zero
      // + requires allowance box to exist
      // + requires allowance box to be zero or zero address balance box to be total supply
      .api_(A.deleteAllowanceBox, (owner, spender) => {
        check(
          isSome(allowances[[owner, spender]]),
          "ARC200: Allowance box not found"
        );
        check(
          arc200.allowance(owner, spender) == UInt256(0),
          "ARC200: Allowance box not empty"
        );
        return [
          (k) => {
            delete allowances[[owner, spender]];
            k(true);
            return [s];
          },
        ];
      })
      // api: destroy
      // - destroy this contract
      // + requires zero address balance box to be total supply
      // + deletes last balance box, zero address balance box
      // + exits loop and closes contract
      .api_(A.destroy, () => {
        check(
          isSome(balances[zeroAddress]),
          "ARC200: Zero address balance box not found"
        );
        check(s.tokenAmount == 0);
        return [
          (k) => {
            delete balances[zeroAddress]; // delete last balance box
            k(null);
            return [{ ...s, closed: true }];
          },
        ];
      });
    commit();
    exit();
  });

//export const wNNT200 = wNT200();