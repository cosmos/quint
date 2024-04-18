# Tests

## Automated Test with simulator

Run

```sh
quint test --main=ics20v2Test ics20v2.qnt --verbosity=2
```

Note that --verbosity=3 is not working. Neither it works for ics20.qnt.

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
