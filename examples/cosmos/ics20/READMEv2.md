# Quint spec of ICS20v2 (Fungible Token Transfer with multidenom and forwarding support)

## Context

This is a formal specification of [ICS20v2](https://github.com/cosmos/ibc/pull/1090) (Fungible Token Transfer) in Quint. This specification is an extension of the of the work done by our colleagues Gabriela Moreira and Thomas Pani at Informal System.

## Tests

Testing topology:

For testing, imagine the following topology between channels in chains A, B and C.
     ┌───────────────────┐           ┌────────────────────────────────────┐         ┌───────────────────┐
     │      Chain A      │           │               Chain B              │         │      Chain C      │
     │                   │           │                                    │         │                   │
     │ ┌───────────────┐ │           │ ┌──────────────┐  ┌──────────────┐ │         │ ┌───────────────┐ │
     │ │               │ │           │ │              │  │              │ │         │ │               │ │
     │ │  channelToB   │◄├───────────┤►│  channelToA  │  │  channelToC  │◄├─────────┤►│  channelToB   │ │
     │ │               │ │           │ │              │  │              │ │         │ │               │ │
     │ └───────────────┘ │           │ └──────────────┘  └──────────────┘ │         │ └───────────────┘ │
     │                   │           │                                    │         │                   │
     └───────────────────┘           └────────────────────────────────────┘         └───────────────────┘

[Visual representation of each testing scenario](https://excalidraw.com/#json=imWPrnjVUYGRX0ruIxjii,bWrrA-vuQx43Sd7Z-pSB2w)

[State transition table of each testing scenario](https://docs.google.com/spreadsheets/d/1XCI6aNBfqDYhdOpzg0tFxaXwWCPRLaRXgiuPzvePRjk/edit#gid=2106405052)  

### Automated Test

Run all tests

```sh
quint test --main=ics20v2Test ics20v2.qnt --verbosity=2 --max-samples=10 
```

To run a specific test change "--match=FScenario1Test" to test name 

```sh
quint test --main=ics20v2Test ics20v2.qnt --verbosity=3 --match=FScenario1Test
```

### Invariant Checker

To run a specific invariant check change --invariant=BalanceNonNegative to other invariant names

```sh
quint run --max-samples=100 --max-steps=100 --invariant=BalanceNonNegative --main=ics20v2Test ics20v2.qnt --verbosity=2
```

### Interactive Test Play Steps

Run

```sh
quint repl -r ics20v2.qnt::ics20v2Test
```
