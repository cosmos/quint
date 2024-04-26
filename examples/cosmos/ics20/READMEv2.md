# Tests

[Visual representation of each testing scenario](https://excalidraw.com/#json=imWPrnjVUYGRX0ruIxjii,bWrrA-vuQx43Sd7Z-pSB2w)

[State transition table of each testing scenario](https://docs.google.com/spreadsheets/d/1XCI6aNBfqDYhdOpzg0tFxaXwWCPRLaRXgiuPzvePRjk/edit#gid=2106405052)  

## Automated Test

Run all tests

```sh
quint test --main=ics20v2Test ics20v2.qnt --verbosity=2
```

To run a specific test change --match=Scenario1Test number from 1 to 5

```sh
quint test --main=ics20v2Test ics20v2.qnt --verbosity=3 --match=Scenario1Test
```

## Invariant Checker

To run a specific invariant check change --invariant=BalanceNonNegative to other invariant names

```sh
quint run --max-samples=1000 --max-steps=1000 --invariant=BalanceNonNegative --main=ics20v2Test ics20v2.qnt --verbosity=2
```

## Interactive Test Play Steps

Run

```sh
quint repl -r ics20v2.qnt::ics20v2Test
```

### Test 1

Manual Execution of send, recv, and ack packets

```sh
setBalanceIn("A", "alice", ATOM, 100)
sendPacket("A", "B", ATOM, 20, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
chainStates.get("A")
chainStates.get("B")
receivePacket("A", "B")
chainStates.get("A")
chainStates.get("B")
```

```sh
sendPacket("B", "C", { baseDenom: "atom", path: [{ channel: "channelToA", port: "transfer" }]}, 20, "escrow_account", "charlie",[])
receivePacket("B", "C")
chainStates.get("A")
chainStates.get("B")
chainStates.get("C")
```

```sh
receiveAck("B")
receiveAck("A")
chainStates.get("A")
chainStates.get("B")
chainStates.get("C")
```

### test 2

```sh
setBalanceIn("A", "alice", ATOM, 100)
sendTransfer("A", "B", ATOM, 20, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
```

We need to execute this second on to actually forward the packet unlees we change sendTransfer 

```sh
sendTransfer("B", "C", { baseDenom: "atom", path: [{ channel: "channelToA", port: "transfer" }]}, 20, "escrow_account", "charlie",[])
```
