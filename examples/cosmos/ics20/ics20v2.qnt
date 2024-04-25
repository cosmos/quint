// -*- mode: Bluespec; -*-

/**
 * A specification of the ICS20 fungible token transfer protocol:
 * https://github.com/cosmos/ibc/tree/main/spec/app/ics-020-fungible-token-transfer
 *
 * Gabriela Moreira and Thomas Pani, Informal Systems, 2023
 */
module ics20v2 {
  import base.* from "./base"
  import bank.* from "./bank"
  import denomTrace.* from "./denomTrace"

  /****************************************************************************
   * TYPES
   ***************************************************************************/

  // Fundamental types
  type Height = int
  type ForwardingPath= List[HopElement]

  // IBC packet types
  type FungibleTokenData = {
    denom: DenomTrace,
    amount: UINT256,
    sender: Address,
    receiver: Address,
    memo: str, 
    forwardingPath: ForwardingPath // Adding forwarding on V1 data packets 
  }

  type Packet = {
    data: FungibleTokenData,
    sourcePort: str,
    sourceChannel: Channel,
    destPort: str,
    destChannel: Channel,
  }

  type FungibleTokenPacketAcknowledgement = {
    success: bool,
    errorMessage: str,
    packet: Packet  // the acknowledged packet
  }

  /// State of the IBC module in a chain
  type ChainState = {
    bank: Accounts,
    channels: ChannelCounterparties,
    channelEscrowAddresses: Channel -> Address,
    channelForwardingAddresses: Channel -> Address, //Needed? 
    // IBC packet handling:
    outPackets: Set[Packet],                        // outgoing unreceived packets
    receivedButUnacknowledgedPackets: Set[Packet],  // received but unacknowledged packets
    inAcknowledgements: Set[FungibleTokenPacketAcknowledgement],  // incoming acknowledgements
    inTimeouts: Set[Packet], // incoming timeouts
    forwardedPacket: List[Packet], //packetForwardPath                                
  }

 // NOT USED TYPES. 
 //These type will be useful to define the multi-denom which is not currently supported 
  // Ics20v2 types
  type Token = {
  denom: DenomTrace,
  //trace: str, contained in DenomTrace which has baseDenom and Path   
  amount: UINT256 
  }

   // IBC packetV2 types
  type FungibleTokenDataV2= {
    Tokens: List[Token], 
    sender: Address,
    receiver: Address,
    memo: str,
    forwardingPath: List[str]
  }

  type PacketV2 = {
    data: FungibleTokenDataV2,
    sourcePort: str,
    sourceChannel: Channel,
    destPort: str,
    destChannel: Channel,
  }
  
    type FungibleTokenPacketAcknowledgementV2 = {
    success: bool,
    errorMessage: str,
    packet: PacketV2  // the acknowledged packet
  }

type ChainStateV2 = {
    bank: Accounts,
    channels: ChannelCounterparties,
    channelEscrowAddresses: Channel -> Address,
    // IBC packet handling:
    outPackets: Set[PacketV2],                        // outgoing unreceived packets
    receivedButUnacknowledgedPackets: Set[PacketV2],  // received but unacknowledged packets
    inAcknowledgements: Set[FungibleTokenPacketAcknowledgementV2],  // incoming acknowledgements
    inTimeouts: Set[PacketV2],                                      // incoming timeouts
  }

  /****************************************************************************
   * FUNCTIONAL LAYER
   ***************************************************************************/

  /****************************/
  /*     helper functions     */
  /****************************/

  /// The counterparty for a channel `C` in a chain is the channel identifier of
  /// the channel `C` connects to, in the other chain.
  pure def getCounterparty(chainState: ChainState, sourceChannel: Channel): Channel = {
    chainState.channels.get(sourceChannel)
  }

  /****************************/
  /*     public interface     */
  /****************************/

 // For Token forwarding without MultiDenom support 
 // Only modification needed to sendFungibleTokens are: 
 // 1. Pass forwadingPath as a function parameter   
 // 2. Pass the forwardingPath into the data
 pure def sendFungibleTokens(chainState: ChainState, denomination: DenomTrace, amount: UINT256,
                              sender: Address, receiver: Address, forwardingPath: ForwardingPath, sourcePort: str, sourceChannel: Channel,
                              timeoutHeight: Height, timeoutTimestamp: uint64): ChainState = {
    
    pure val bankResult = if (movingBackAlongTrace(denomination, { port: sourcePort, channel: sourceChannel })) {
      // burn vouchers
      (chainState.bank).BurnCoins(sender, denomination, amount)
    } else {
      // escrow tokens
      pure val escrowAccount = chainState.channelEscrowAddresses.get(sourceChannel)
      chainState.bank.TransferCoins(sender, escrowAccount, denomination, amount)
    }

    if (bankResult.success) {
      pure val data = { denom: denomination, amount: amount, sender: sender, receiver: receiver, memo: "", forwardingPath: forwardingPath }

      // handler.sendPacket
      pure val packet = {
        data: data,
        sourcePort: sourcePort,
        sourceChannel: sourceChannel,
        destPort: "transfer",
        destChannel: getCounterparty(chainState, sourceChannel),
      }

      chainState
        .with("bank", bankResult.accounts)
        .with("outPackets", chainState.outPackets.union(Set(packet)))
    } else {
      chainState
    }
    
  }

// Helper functions for onRecvPacket Logic execution
  pure def assignCFA(address: Address, chainState: ChainState, packet: Packet): str = {
    if(chainState.channelForwardingAddresses.get(packet.destChannel)==""){
        (address) // Pass in MOCK ADDRESS or WRITE NEW ADDRESS FUNCTION  
    }else (chainState.channelForwardingAddresses.get(packet.destChannel))   
    }

  pure def assignRecvAddress(FPexists: bool, packet: Packet, address: Address): (str,str) = {
    if(FPexists){
        pure val receiver = address 
        pure val finalReceiver = packet.data.receiver
        (receiver,finalReceiver)
    } else{
        pure val receiver = packet.data.receiver
        (receiver,"")
    }
  }

  pure def getNextPortChannel(forwardingPath: ForwardingPath): (str, str, List[HopElement]) = {
    if (forwardingPath==[]) {
    // Handle the case where the forwarding path is empty
    ("","", [])  // Returning empty strings for port and channel and an empty list for the path
  } else {
    pure val headElement = forwardingPath.head()  // Get the first element
    pure val nextPort = headElement.port   // Get NextPort
    pure val nextChannel = headElement.channel   // Get NextChannel
    pure val newForwardingPath= forwardingPath.tail() // Delete first element of the forwardingPath
    (nextPort,nextChannel,newForwardingPath)
  }
  }


  /// `onRecvPacket` should return an acknowledgment, but it also has to update
  /// the chain state, so the return type is the updated value for the chain
  /// state and the acknowledgment
  pure def onRecvPacket(chainState: ChainState, packet: Packet): (ChainState, FungibleTokenPacketAcknowledgement) = {
    pure val data = packet.data
    
    // Addresses assignment. Helper functions define spec logic for assignment 
    pure val channelForwardingAddress= assignCFA("forward_account", chainState, packet)
    pure val addressTuple=assignRecvAddress(data.forwardingPath!=[],packet, channelForwardingAddress)
    pure val receiver = addressTuple._1
    pure val finalReceiver = addressTuple._2 
    
    // Note that for quint is better not the preconstruct a succesfull ack 
    // but rather to assign it to true of false when needed
    
    pure val movingBack = movingBackAlongTrace(data.denom, { port: packet.sourcePort, channel: packet.sourceChannel })
    pure val newDenom = updateTrace(movingBack, data.denom, { port: packet.destPort, channel: packet.destChannel })

    // result is a pair of 1. a BankResult and 2. an error message that is used in case BankResult.success = false
    pure val result = if (movingBack) {
      // unescrow tokens to receiver
      pure val escrowAccount = chainState.channelEscrowAddresses.get(packet.destChannel)
      pure val bankResult = chainState.bank.TransferCoins(escrowAccount, receiver, newDenom, data.amount)

      (bankResult, "transfer coins failed")
    } else {
      // mint vouchers to receiver
      pure val bankResult = chainState.bank.MintCoins(receiver, newDenom, data.amount)

      (bankResult, "mint coins failed")
    }

    pure val bankResult = result._1
    pure val errorMessage = result._2

    
    pure val ack = if (bankResult.success) {
      { success: true, errorMessage: "", packet: packet }
    } else {
      { success: false, errorMessage: errorMessage, packet: packet }
    }

    if(ack.success==false){
      (chainState,ack)
    }
    // Otherwise proceed with token forwarding logic. 
    else {
      if(data.forwardingPath!=[]){

        pure val tempChainState = chainState.with("bank", bankResult.accounts)

        pure val nextStuff=getNextPortChannel(data.forwardingPath)
        pure val nextPort=nextStuff._1
        pure val nextChannel=nextStuff._2
        pure val newForwardingPath=nextStuff._3

        pure val newTempChainState = sendFungibleTokens(tempChainState, data.denom, data.amount,
                              receiver, finalReceiver, newForwardingPath, nextPort, nextChannel,
                              10,10) // Which Timeout?  
        // store packet for future sending ack
        pure val newChainState = newTempChainState.with("forwardedPacket", [packet])
        (newChainState,ack)
      }
        else{
        
        pure val tempChainState = chainState.with("bank", bankResult.accounts)
        //pure val nilAck= { success: "", errorMessage: "", packet: packet }
        (tempChainState, ack) // Here we should return nil for the ack 
      }
      }
    
  }
  
  /// Refund tokens from a token transfer initiated by `packet`.
  ///
  /// Should be called if the token transfer fails on the receiver chain
  /// (due to a packet acknowledgement indicating failure, or due to a timeout).
  ///
  /// In particular, `refundTokens` is called by both `onAcknowledgePacket` (on
  /// failure) and by `onTimeoutPacket`, to refund burnt or escrowed tokens to
  /// the original sender.
  ///
  /// `packet`: The packet (originally sent from the local chain) that initiated the token transfer.
  ///           Packet `packet` should have resulted in a failed acknowledgement or timeout.
  pure def refundTokens(chainState: ChainState, packet: Packet): ChainState = {
    pure val data: FungibleTokenData = packet.data
    pure val source: HopElement = { port: packet.sourcePort, channel: packet.sourceChannel }
    pure val bankResult =
      if (movingBackAlongTrace(data.denom, source)) {
        // The (failed) transfer attempt was moving the token back along its denom trace.
        // For this, we originally burnt vouchers in `sendFungibleTokens`, so mint them back.
        chainState.bank.MintCoins(data.sender, data.denom, data.amount)
      } else {
        // The (failed) transfer attempt was moving the token further along its denom trace.
        // For this, we originally escrowed tokens in `sendFungibleTokens`, so unescrow them back.
        pure val escrowAccount = chainState.channelEscrowAddresses.get(packet.sourceChannel)
        chainState.bank.TransferCoins(escrowAccount, data.sender, data.denom, data.amount)
      }
    if (bankResult.success) {
      chainState.with("bank", bankResult.accounts)
    } else {
      // TODO: ICS 20 does not specify what happens if the bank modules return an error.
      //       We treat bank failure as a noop.
      chainState
    }
  }
 
 //Helper function for onAck logic executinon
 pure def eventuallyRefund(chainState: ChainState, packet: Packet, acknowledgement: FungibleTokenPacketAcknowledgement): ChainState ={
      if (acknowledgement.success==false) {
       pure val newChainState= refundTokens(chainState, packet)
      newChainState 
      }else chainState
 }
 
  /// Called by the routing module when a packet sent by this module has been acknowledged.
  pure def onAcknowledgePacket(chainState: ChainState, packet: Packet,
                               acknowledgement: FungibleTokenPacketAcknowledgement) : (ChainState) = {
      
      // check if the packet that was sent is from a previously forwarded packet
      if(chainState.forwardedPacket!=[]){
          pure val prevPacket=chainState.forwardedPacket.head() 
          if (acknowledgement.success) {
              // The acknowledgment get written in the action for simuliation purposes. 
              //pure val ack ={ success: true, errorMessage: "forwarded packet succeeded", packet: prevPacket }
              //val newInAcknowledgements = tempChainState.inAcknowledgements.union(Set(ack))
              //pure val newChainState= tempChainState.with("inAcknowledgements", newInAcknowledgements)
              // No Op 
              chainState
          } else {
                // the forwarded packet has failed, thus the funds have been refunded to the forwarding address.
                // we must revert the changes that came from successfully receiving the tokens on our chain
                // before propogating the error acknowledgement back to original sender chain        
                pure val revertedChainState=revertInFlightChanges(chainState,packet,prevPacket)
                // The acknowledgment get written in the action for simuliation purposes.
                // write error acknowledgement
                //pure val ack ={ success: false, errorMessage: "forwarded packet failed", packet: prevPacket }
                //val newInAcknowledgements = revertedChainState.inAcknowledgements.union(Set(ack))
                //pure val newChainState= revertedChainState.with("inAcknowledgements", newInAcknowledgements)
                revertedChainState
                }
      }else {
        // if the transfer failed, refund the tokens
      pure val tempChainState = eventuallyRefund(chainState, packet, acknowledgement)
      tempChainState
      } 
        
  }

  /// Called by the routing module when a packet sent by this module has timed out
  /// (such that it will not be received on the destination chain).
  pure def onTimeoutPacket(chainState: ChainState, packet: Packet): (ChainState)  = {
    // check if the packet was sent is from a previously forwarded packet
    pure val prevPacket=chainState.forwardedPacket.head()
    if(chainState.forwardedPacket!=[]){
      // the forwarded packet has failed, thus the funds have been refunded to the forwarding address.
      // we must revert the changes that came from successfully receiving the tokens on our chain
      // before propogating the error acknowledgement back to original sender chain
      pure val tempChainState=revertInFlightChanges(chainState,packet,prevPacket)
      // write error acknowledgement
      // The acknowledgment get written in the action for simuliation purposes.
      //pure val ack ={ success: false, errorMessage: "forwarded packet failed", packet: prevPacket }
      //val newInAcknowledgements = tempChainState.inAcknowledgements.union(Set(ack))
      //pure val newChainState= tempChainState.with("inAcknowledgements", newInAcknowledgements)
      tempChainState
      }
      else {
        // the packet timed out, so refund the tokens
        pure val refundChainState=refundTokens(chainState, packet)
        refundChainState
      }
  }

// Helper Function revertInFlightChanges
// Version without Multidenom Support 
// revertInFlightChanges reverts the receive packet and send packet
// that occurs in the middle chains during a packet forwarding
// If an error occurs further down the line, the state changes
// on this chain must be reverted before sending back the error acknowledgement
// to ensure atomic packet forwarding
pure def revertInFlightChanges(chainState: ChainState, sentPacket: Packet, receivedPacket: Packet): ChainState = {
 pure val forwardEscrow = chainState.channelEscrowAddresses.get(sentPacket.sourceChannel)
 pure val reverseEscrow = chainState.channelEscrowAddresses.get(receivedPacket.destChannel)
 pure val hopElementSent = {port: sentPacket.sourcePort, channel: sentPacket.sourceChannel}
 pure val hopElementRecv = {port: receivedPacket.destPort, channel: receivedPacket.destChannel}
 // check if the packet we sent out was sending as source or not
 // in this case we escrowed the outgoing tokens
 pure val bankResult =
      if (movingBackAlongTrace(sentPacket.data.denom, hopElementSent)) {
          // If we are here the packet we sent out was sending as source 
          // check if the packet we received was a source token for our chain
          if (movingBackAlongTrace(receivedPacket.data.denom, hopElementRecv)) {
              // if we are here the packet we received was a source token for our chain 
              // receive sent tokens from the received escrow to the forward escrow account
              // so we must send the tokens back from the forward escrow to the original received escrow account
              
              chainState.bank.TransferCoins(forwardEscrow, reverseEscrow, sentPacket.data.denom, sentPacket.data.amount)
          }
          else {
              // if we are here the packet we received was a not source token for our chain

              // receive minted vouchers and sent to the forward escrow account
              // so we must remove the vouchers from the forward escrow account and burn them
              // THIS FIX MAKE SCENARIO 3,5 TEST PASS. NEED TO INSPECT DEEPER. 
              //chainState.bank.MintCoins(reverseEscrow, sentPacket.data.denom, sentPacket.data.amount)
              // Original Line
              chainState.bank.BurnCoins(forwardEscrow, sentPacket.data.denom, sentPacket.data.amount)
            }
    } else {
          // in this case we burned the vouchers of the outgoing packets
          // check if the packet we received was a source token for our chain
          // in this case, the tokens were unescrowed from the reverse escrow account
          if (movingBackAlongTrace(receivedPacket.data.denom, hopElementRecv)){
            // in this case we must mint the burned vouchers and send them back to the escrow account
              
            chainState.bank.MintCoins(reverseEscrow, sentPacket.data.denom, sentPacket.data.amount)
          }else{
            // if it wasn't a source token on receive, then we simply had minted vouchers and burned them in the receive.
            // So no state changes were made, and thus no reversion is necessary
            // THIS FIX MAKE SCENARIO 2 TEST PASS but Scenario1 to Fail. NEED TO INSPECT DEEPER. 
            //chainState.bank.BurnCoins(reverseEscrow, sentPacket.data.denom, sentPacket.data.amount)
            // Original Line
            // No Op Miniting 0 Tokens 
            // With No Op SCENARIO 1 TEST PASS but Scenario 2 to Fail. NEED TO INSPECT DEEPER. 
            chainState.bank.MintCoins(reverseEscrow, sentPacket.data.denom, 0)
            }
          }
      
      if (bankResult.success) {
      chainState.with("bank", bankResult.accounts)
    } else {
      // TODO: ICS 20 does not specify what happens if the bank modules return an error.
      //       We treat bank failure as a noop.
      chainState
    }
}

} // Module closing bracket 

module ics20v2Test {
  import base.* from "./base"
  import bank.getBalance from "./bank"
  import bank.getBalances from "./bank"
  import ics20v2.*

  /****************************************************************************
   * STATE MACHINE
   ***************************************************************************/

  /// Map from chain identifiers to their state
  var chainStates: str -> ChainState

  /// Map from chain identifiers to a map of the chain identifiers it can
  /// communicate with and the channel to be used to send packets. For example,
  /// chain A connects to chain B through channel "channelToB".
  /// Testing Topology: 
  // For testing, imagine the following topology between channels in chains A, B and C.
  // PS: There should be similar channels between A and C, those are ommited in the diagram for simplicity
  // ┌───────────────────┐           ┌────────────────────────────────────┐         ┌───────────────────┐
  // │      Chain A      │           │               Chain B              │         │      Chain C      │
  // │                   │           │                                    │         │                   │
  // │ ┌───────────────┐ │           │ ┌──────────────┐  ┌──────────────┐ │         │ ┌───────────────┐ │
  // │ │               │ │           │ │              │  │              │ │         │ │               │ │
  // │ │  channelToB   │◄├───────────┤►│  channelToA  │  │  channelToC  │◄├─────────┤►│  channelToB   │ │
  // │ │               │ │           │ │              │  │              │ │         │ │               │ │
  // │ └───────────────┘ │           │ └──────────────┘  └──────────────┘ │         │ └───────────────┘ │
  // │                   │           │                                    │         │                   │
  // └───────────────────┘           └────────────────────────────────────┘         └───────────────────┘

  pure val CHANNEL_TOPOLOGY = Map(
    "A" -> Map(
      "B" -> "channelToB"
    ),
    "B" -> Map(
      "A" -> "channelToA",
      "C" -> "channelToC"
    ),
    "C" -> Map(
      "B" -> "channelToB"
    )
  )
  pure val CHAINS = CHANNEL_TOPOLOGY.keys()

  /// For each chain, a map from channel to their channel counterparties,
  /// derived from `CHANNEL_TOPOLOGY`. For example, in chain A, channel "channelToB"
  /// has the counterparty "channelToA".
  pure val channelCounterparties: str -> Channel -> Channel = CHAINS.mapBy(chain => {
    pure val connectedChains = CHANNEL_TOPOLOGY.get(chain).keys()
    connectedChains.map(counterpartyChain => {
      pure val localChannel = CHANNEL_TOPOLOGY.get(chain).get(counterpartyChain)
      pure val counterpartyChannel = CHANNEL_TOPOLOGY.get(counterpartyChain).get(chain)
      (localChannel, counterpartyChannel)
    }).setToMap()
  })

  // Probably Need To change this function and the way it's used to proceed with forwarding 
  /// Return true iff there is a channel from `sourceChain` to `destChain` defined in `CHANNEL_TOPOLOGY`.
  ///
  /// In particular, this returns false if `sourceChain == destChain`.
  pure def hasChannelBetween(sourceChain: str, destChain: str): bool = all {
    // ICS 4: "a channel is a pipeline [...] between specific modules on **separate** blockchains"
    sourceChain != destChain,
    // there is a channel between `sourceChain` and `destChain`
    CHANNEL_TOPOLOGY.has(sourceChain),
    CHANNEL_TOPOLOGY.get(sourceChain).has(destChain),
  }

  /// Return true iff there is a channel from `sourceChain` to `destChain` defined in `CHANNEL_TOPOLOGY`
  /// that corresponds to the channel endpoints of `packet`.
  pure def isTravelingBetween(packet: Packet, sourceChain: str, destChain: str): bool = all {
    // there is a channel between `sourceChain` and `destChain`
    hasChannelBetween(sourceChain, destChain),
    // packet endpoints correspond to channel ends
    channelCounterparties.get(sourceChain).has(packet.sourceChannel),
    channelCounterparties.get(sourceChain).get(packet.sourceChannel) == packet.destChannel
  }

  /* Helper operators to manipulate bank state */
  /// Sets the balance of `account` in `chain` to `amount` of `denom`.
  action setBalanceIn(chain, account, denom, amount) = {
    chainStates' = chainStates.setBy(chain, state =>
      state.with("bank", state.bank.setBy(account, balances => balances.set(denom, amount)))
    )
  }

  /// Gets the balance of `account` in `chain` of `denom`.
  def getBalanceIn(chain, account, denom) = {
    chainStates.get(chain).bank.getBalances(account).getBalance(denom)
  }

  /// Send a packet from `sourceChain` to `destChain`, indicating a transfer
  /// of `amount`-many tokens of `denom` from `sender` to `receiver`.
  action sendPacket(sourceChain: str, destChain: str,
                    denom: DenomTrace, amount: UINT256,
                    sender: Address, receiver: Address, forwardingPath: ForwardingPath): bool = all {
    // (1) Pre-condition:
    // there is a channel between `sourceChain` and `destChain`
    hasChannelBetween(sourceChain, destChain),

    // Extract Forwarding Path 
    // (2) Send the packet using `sendFungibleTokens`:
    val sourceChainState = chainStates.get(sourceChain)
    val newSourceChainState = sendFungibleTokens(sourceChainState, denom, amount,
                                                 sender, receiver, forwardingPath, 
                                                 "transfer", CHANNEL_TOPOLOGY.get(sourceChain).get(destChain),
                                                 0, 0)

    // (3) Quint state transition:
    chainStates' = chainStates.set(sourceChain, newSourceChainState)
  }

  // Mock Function to fake an error 
  action failingReceivePacket(sourceChain: str, destChain: str): bool =
    val sourceChainState = chainStates.get(sourceChain)
    all {
      // (1) Pre-condition:
      // there is a channel between `sourceChain` and `destChain`
      hasChannelBetween(sourceChain, destChain),
      // there is an unreceived packet traveling from `sourceChain` to `destChain`
      sourceChainState.outPackets.exists(packet => packet.isTravelingBetween(sourceChain, destChain)),

      // (2) Non-deterministically pick a packet from `sourceChain` to receive on `destChain`:
      nondet packet = sourceChainState.outPackets
                                  .filter(p => p.isTravelingBetween(sourceChain, destChain))
                                  .oneOf()
      all {
        // (3) Compute updated destination chain state: call `onRecvPacket` callback:
        val recvResult = onRecvPacket(chainStates.get(destChain), packet)
        val newDestChainState = recvResult._1
        val acknowledgement   = recvResult._2
        val ack = { success: false, errorMessage: "Injected Failure", packet: packet }
        // (4) Compute updated source chain state:
        // Update packet sets, moving `packet` from `outPackets` to `receivedButUnacknowledgedPackets`
        // (this simulates ICS 4 exactly-once packet delivery)
        val newSourceChainOutPackets = sourceChainState.outPackets.exclude(Set(packet))
        val newSourceChainUnackPackets = sourceChainState.receivedButUnacknowledgedPackets.union(Set(packet))
        // Update set `inAcknowledgements` to include the sent but (yet) unprocessed `acknowledgement`

        //val newSourceChainInAcknowledgements = sourceChainState.inAcknowledgements.union(Set(acknowledgement))
        val newSourceChainInAcknowledgements = sourceChainState.inAcknowledgements.union(Set(ack))
        
        // Update source chain state with new packet/acknowledgement sets
        val newSourceChainState   = sourceChainState
                                          .with("outPackets", newSourceChainOutPackets)
                                          .with("receivedButUnacknowledgedPackets", newSourceChainUnackPackets)
                                          .with("inAcknowledgements", newSourceChainInAcknowledgements)
        
        // (5) Quint state transition:
        chainStates' = chainStates
                          //.set(destChain, newDestChainState)
                          .set(destChain, chainStates.get(destChain))
                          .set(sourceChain, newSourceChainState)
      }
    }
  /// Receive a packet sent from `sourceChain` to `destChain`:
  /// - Pick an arbitrary, previously unreceived packet sent from `sourceChain` to `destChain`.
  /// - Call the `onRecvPacket` callback on it.
  /// - Update the chain states to record the packet as received.
  /// - Record (but not receive) the acknowledgement produced by `onRecvPacket` on `destChain`.
  action receivePacket(sourceChain: str, destChain: str): bool =
    val sourceChainState = chainStates.get(sourceChain)
    all {
      // (1) Pre-condition:
      // there is a channel between `sourceChain` and `destChain`
      hasChannelBetween(sourceChain, destChain),
      // there is an unreceived packet traveling from `sourceChain` to `destChain`
      sourceChainState.outPackets.exists(packet => packet.isTravelingBetween(sourceChain, destChain)),

      // (2) Non-deterministically pick a packet from `sourceChain` to receive on `destChain`:
      nondet packet = sourceChainState.outPackets
                                  .filter(p => p.isTravelingBetween(sourceChain, destChain))
                                  .oneOf()
      all {
        // (3) Compute updated destination chain state: call `onRecvPacket` callback:
        val recvResult = onRecvPacket(chainStates.get(destChain), packet)
        val newDestChainState = recvResult._1
        val acknowledgement   = recvResult._2

        // (4) Compute updated source chain state:
        // Update packet sets, moving `packet` from `outPackets` to `receivedButUnacknowledgedPackets`
        // (this simulates ICS 4 exactly-once packet delivery)
        val newSourceChainOutPackets = sourceChainState.outPackets.exclude(Set(packet))
        val newSourceChainUnackPackets = sourceChainState.receivedButUnacknowledgedPackets.union(Set(packet))
        // Update set `inAcknowledgements` to include the sent but (yet) unprocessed `acknowledgement`
        val newSourceChainInAcknowledgements = sourceChainState.inAcknowledgements.union(Set(acknowledgement))
        // Update source chain state with new packet/acknowledgement sets
        
        val newSourceChainState   = sourceChainState
                                          .with("outPackets", newSourceChainOutPackets)
                                          .with("receivedButUnacknowledgedPackets", newSourceChainUnackPackets)
                                          .with("inAcknowledgements", newSourceChainInAcknowledgements)
        
        // (5) Quint state transition:
        chainStates' = chainStates
                          .set(destChain, newDestChainState)
                          .set(sourceChain, newSourceChainState)
      }
    }

  /// Time out a packet sent from `sourceChain` to `destChain`.
  action timeoutPacket(sourceChain: str, destChain: str): bool =
    val sourceChainState = chainStates.get(sourceChain)
    all {
      // (1) Pre-condition:
      // there is a channel between `sourceChain` and `destChain`
      hasChannelBetween(sourceChain, destChain),
      // there is an unreceived packet traveling from `sourceChain` to `destChain`
      sourceChainState.outPackets.exists(packet => packet.isTravelingBetween(sourceChain, destChain)),

      // (2) Non-deterministically pick a packet from `sourceChain` to `destChain` to time out:
      nondet packet = sourceChainState.outPackets
                                  .filter(p => p.isTravelingBetween(sourceChain, destChain))
                                  .oneOf()

      // (3) Compute updated source chain state:
      // Update packet sets, moving `packet` from `outPackets` to `inTimeouts`
      val newSourceChainOutPackets = sourceChainState.outPackets.exclude(Set(packet))
      val newSourceChainInAcknowledgements = sourceChainState.inTimeouts.union(Set(packet))
      // Update source chain state with new packet/acknowledgement sets
      val newSourceChainState = sourceChainState
                                      .with("outPackets", newSourceChainOutPackets)
                                      .with("inTimeouts", newSourceChainInAcknowledgements)

      // (4) Quint state transition:
      chainStates' = chainStates.set(sourceChain, newSourceChainState)
    }


  
  // This function is meant to be used to test error acks. 
  action forwardAck(forwarderChain: str, receiverChain: str): bool =
    val receiverChainState = chainStates.get(receiverChain)
    val forwarderChainState = chainStates.get(forwarderChain)
    
    all {
      // (1) Pre-condition:
      // there is an incoming acknowledgement
      forwarderChainState.inAcknowledgements.setNonEmpty(),

      // (2) Compute updated chain state:
      // non-deterministically pic an acknowledgement
      nondet acknowledgement = forwarderChainState.inAcknowledgements.oneOf()
      nondet receiverAcknowledgement = receiverChainState.inAcknowledgements.oneOf()
      // call the `onAcknowledgePacket` callback
      val ackedChainState = onAcknowledgePacket(receiverChainState, receiverAcknowledgement.packet, acknowledgement)
      // remove `acknowledgement` from incoming acknowledgements
      val newInAcknowledgements = ackedChainState.inAcknowledgements.exclude(Set(acknowledgement))
      // remove `acknowledgement.packet` from receivedButUnacknowledgedPackets
      
      val newInUnackPackets = ackedChainState.receivedButUnacknowledgedPackets.exclude(Set(acknowledgement.packet))
      
      val newChainState = ackedChainState.with("inAcknowledgements", newInAcknowledgements)
                                         .with("receivedButUnacknowledgedPackets", newInUnackPackets)

      // (3) Quint state transition:
      chainStates' = chainStates.set(receiverChain, newChainState)
    }


  /// Receive an acknowledgement on `chain`:
  /// - Pick an arbitrary, previously unreceived acknowledgement on `chain`.
  /// - Call the `onAcknowledgePacket` callback on it.
  /// - Update the chain state to record the acknowledgement as received.
  action receiveAck(chain: str): bool =
    val chainState = chainStates.get(chain)
    
    all {
      // (1) Pre-condition:
      // there is an incoming acknowledgement
      chainState.inAcknowledgements.setNonEmpty(),

      // (2) Compute updated chain state:
      // non-deterministically pic an acknowledgement
      nondet acknowledgement = chainState.inAcknowledgements.oneOf()
      // call the `onAcknowledgePacket` callback
      val ackedChainState = onAcknowledgePacket(chainState, acknowledgement.packet, acknowledgement)
      // remove `acknowledgement` from incoming acknowledgements
      if(acknowledgement.success==true){
        val newInAcknowledgements = ackedChainState.inAcknowledgements.exclude(Set(acknowledgement))
        // remove `acknowledgement.packet` from receivedButUnacknowledgedPackets
        val newInUnackPackets = ackedChainState.receivedButUnacknowledgedPackets.exclude(Set(acknowledgement.packet))
        val newChainState = ackedChainState.with("inAcknowledgements", newInAcknowledgements)
                                         .with("receivedButUnacknowledgedPackets", newInUnackPackets)

        // (3) Quint state transition:
        chainStates' = chainStates.set(chain, newChainState)
    }
    else{
        // Write the ack to Preserve the failed ack to subsequent forwarding.  
        val newInAcknowledgements = ackedChainState.inAcknowledgements.union(Set(acknowledgement))
        // remove `acknowledgement.packet` from receivedButUnacknowledgedPackets
        val newInUnackPackets = ackedChainState.receivedButUnacknowledgedPackets.exclude(Set(acknowledgement.packet))
        val newChainState = ackedChainState.with("inAcknowledgements", newInAcknowledgements)
                                         .with("receivedButUnacknowledgedPackets", newInUnackPackets)

        // (3) Quint state transition:
        chainStates' = chainStates.set(chain, newChainState)
    }

    }

  /// Receive a timeout on `chain`:
  /// - Pick an arbitrary, previously unreceived timeout on `chain`.
  /// - Call the `onTimeoutPacket` callback on it.
  /// - Update the chain state to record the timeout as received.
  action receiveTimeout(chain: str): bool =
    val chainState = chainStates.get(chain)
    all {
      // (1) Pre-condition:
      // there is a timed out packet
      chainState.inTimeouts.setNonEmpty(),

      // (2) Compute updated chain state:
      // non-deterministically pick a timed out packet
      nondet timedoutPacket = chainState.inTimeouts.oneOf()
      // call the `onTimeout` callback
      val timedoutChainState = onTimeoutPacket(chainState, timedoutPacket)
      // remove `timedoutPacket` from incoming timeouts
      val newInTimeouts = chainState.inTimeouts.exclude(Set(timedoutPacket))
      val newChainState = timedoutChainState.with("inTimeouts", newInTimeouts)

      // (3) Quint state transition:
      chainStates' = chainStates.set(chain, newChainState)
    }

  pure val ATOM = toDenom("atom")
  pure val USER_ACCOUNTS = Set("alice", "bob", "charlie")
  pure val ESCROW_ACCOUNT = "escrow_account"


  // Initialize the protocol
  action initScenario5 = {
    chainStates' = CHAINS.mapBy(chain => {
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: []
    })
  }

  // Take a step in the protocol (non-deterministically chooses one action).
  action step = {
    nondet sourceChain = CHAINS.oneOf()
    nondet destChain = CHAINS.exclude(Set(sourceChain)).oneOf()
    any {
      nondet amount = oneOf(1.to(10))
      nondet sourceAddr = USER_ACCOUNTS.oneOf()
      nondet destAddr = USER_ACCOUNTS.exclude(Set(sourceAddr)).oneOf()
      sendPacket(sourceChain, destChain, ATOM, amount, sourceAddr, destAddr,[]),
      receivePacket(sourceChain, destChain),
      timeoutPacket(sourceChain, destChain),
      receiveAck(sourceChain),
      receiveTimeout(sourceChain),
    }
  }

  /// Send `amount`-many `denom` tokens from `sender` on `sourceChain` to
  /// `receiver` on `destChain`.
  ///
  /// This is a composition of three actions:
  /// 1. sends the packet from `sourceChain` to `destChain`,
  /// 2. receives the packet on `destChain` and produces an acknowledgement, and
  /// 3. receives and processes the acknowledgement on `sourceChain`.
  run sendTransfer(sourceChain: str, destChain: str, denom: DenomTrace, amount: UINT256, sender: Address, receiver: Address, forwadingPath: ForwardingPath): bool = (  
      sendPacket(sourceChain, destChain, denom, amount, sender, receiver,forwadingPath)
    ).then(
      receivePacket(sourceChain, destChain)
    ).then(
      receiveAck(sourceChain)
    )

  /****************************************************************************
   * TESTS
   ***************************************************************************/

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

run DetailedHappyPathTest = {
    pure val amount = 90

    // NOTE: fungible token is prefixed with the full trace in order to verify the packet commitment
    pure val denomInA = ATOM
    pure val denomSentFromAToB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomSentFromBToC = denomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomSentFromAToB.path))
    initScenario5.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      sendPacket("A", "B", ATOM, amount, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(
      receivePacket("A", "B") 
    ).then(
      sendPacket("B", "C", denomSentFromAToB, amount, "forward_account", "charlie",[])
    ).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B")
    ).then(
      receiveAck("A")
    ).then(all {
      // check that the balance is updated on chainC
      val balanceC = getBalanceIn("C", "charlie", denomSentFromBToC)
      assert(balanceC == amount),

      // check that balance on chain B is empty
      val balanceB = getBalanceIn("B", "bob", denomSentFromAToB)
      assert(balanceB == 0),
      // check the escrow_account balance on chain B is amount
      val balanceB2 = getBalanceIn("B", "escrow_account", denomSentFromAToB)
      assert(balanceB2 == amount),

      // check that balance on chain A is empty
      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0),
      // check the escrow_account balance on chain A is amount
      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount),

      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Tansfer happening from A to C using the forwarding path and the sendTransfer previously described. 
  // In quint we need to call twice the sendTransfer to appreciate the state changes.  
  run HappyPathTest = {
    pure val amount = 90

    // NOTE: fungible token is prefixed with the full trace in order to verify the packet commitment
    pure val denomInA = ATOM
    pure val denomSentFromAToB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomSentFromBToC = denomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomSentFromAToB.path))
    initScenario5.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      sendTransfer("A", "B", ATOM, amount, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(all {
      // check that voucher exists on chain B
      val balanceB = getBalanceIn("B", "forward_account", denomSentFromAToB)
      assert(balanceB == amount),

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount),

      sendTransfer("B", "C", denomSentFromAToB, amount, "forward_account", "charlie",[])
    }).then(
      all {
        // check that the balance is updated on chainC
        val balanceC = getBalanceIn("C", "charlie", denomSentFromBToC)
        assert(balanceC == amount),

        // check that balance on chain B is empty
        val balanceB = getBalanceIn("B", "bob", denomSentFromAToB)
        assert(balanceB == 0),
        val balanceB2 = getBalanceIn("B", "escrow_account", denomSentFromAToB)
        assert(balanceB2 == amount),

        val balanceA = getBalanceIn("A", "alice", denomInA)
        assert(balanceA == 0),
        val balanceA = getBalanceIn("A", "escrow_account", denomInA)
        assert(balanceA == amount),

        // noop
      chainStates' = chainStates
      }
    )
  }


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 1 test 
  // Init function for scenario 1 
  action initScenario1 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0), "escrow_account" -> Map(ATOM -> 0)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: []
    })
  }

// Scenario 1 test 
    run Scenario1Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    
    pure val denomBC = denomInA.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomInA.path))
    
    pure val denomBCB = denomInA
    
    pure val denomCBA = denomBCB.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomBCB.path))
    
    initScenario1.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("B", "bob", ATOM, amount)
    ).then({
      // Normal Transfer B to C
      sendPacket("B", "C", denomInA, amount, "bob", "charlie",[])
    }
    ).then(all{
      
       val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 
     
      receivePacket("B", "C") 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == amount),

      receiveAck("B") 
    }).then(all{
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 
      // No Op. Nothing Happened
      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", denomBC, amount, "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 
      // This time token get burned 
      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == 0),

      val balanceC = getBalanceIn("C", "escrow_account", denomBC)
      assert(balanceC == 0),
      
      receivePacket("C", "B") 
    }).then(all{
      val balanceB2 = getBalanceIn("B", "forward_account", denomInA)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == 0),   

      val balanceC = getBalanceIn("C", "escrow_account", denomBC)
      assert(balanceC == 0),  

      sendPacket("B", "A", denomInA, amount, "forward_account", "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", "forward_account", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      failingReceivePacket("B", "A") 
        
    }).then(
      receiveAck("B") // Refund logic should be properly executed on B
    ).then(all{
      val balanceB = getBalanceIn("B", "forward_account", denomInA)
      assert(balanceB == 0), // In the case nothing to revert
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), // This should have been reverted to original state before start forwarding transfer. 
      
      //receiveAck("C")
      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 

      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomInA)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == amount),
      
      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Need to model the concept of different forward and escrow accounts
 // Init function for scenario 2 
  action initScenario2 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "C") Map("charlie" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: []
    })
  }

    run Scenario2Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    pure val denomCB = denomInA.with("path", [{ port: "transfer", channel: "channelToC" }].concat(denomInA.path))
    pure val denomBA = denomCB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomCB.path))
    
    initScenario2.then(
      // Make sure that charlie has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("C", "charlie", ATOM, amount)
    ).then(all{
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 

      val balanceB = getBalanceIn("B", "bob", denomCB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomCB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomCB)
      assert(balanceB3 == 0), 

      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == amount),
        
      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == 0),
      
      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0), 

      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", denomInA, amount, "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      
      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == 0),

      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == amount),

      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0),

      receivePacket("C", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", "forward_account", denomCB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", "escrow_account", denomCB)
      assert(balanceB2 == 0),   

      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == 0),

      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == amount),

      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0),
      

      sendPacket("B", "A", denomCB, amount, "forward_account", "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", "forward_account", denomCB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomCB)
      assert(balanceB2 == amount), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      failingReceivePacket("B", "A") 
        
    }).then(all{
      
      val balanceA = getBalanceIn("A", "alice", denomBA)
      assert(balanceA == 0), 

      val balanceA2 = getBalanceIn("A", "escrow_account", denomBA)
      assert(balanceA2 == 0), // This should have been reverted to original state before start forwarding transfer. 
      
      val balanceA3 = getBalanceIn("A", "forward_account", denomBA)
      assert(balanceA3 == 0), 


      receiveAck("B") // Refund logic should be properly executed on B
    }).then(all{
      val balanceB = getBalanceIn("B", "forward_account", denomCB)
      assert(balanceB == 0), 

      val balanceB2 = getBalanceIn("B", "escrow_account", denomCB)
      assert(balanceB2 == 0), // This should have been reverted to original state before start forwarding transfer. 
      
      //receiveAck("C")
      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 

      val balanceB = getBalanceIn("B", "bob", denomCB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomCB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomCB)
      assert(balanceB3 == 0), 

      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == amount),
        
      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == 0),
      
      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0), 


      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 3 test 

 action initScenario3 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: []
    })
  }




    run Scenario3Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    pure val denomAB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomABC = denomAB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomAB.path))
    

    pure val denomBC = denomInA.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomInA.path))
    
    pure val denomBCB = denomInA
    
    pure val denomCBA = denomBCB.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomBCB.path))
    
    initScenario3.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then({
      // Forwarding Transfer A to C is composed of Forwarding Transfer A to B and B to C
      // Forwarding Transfer A to B
      sendPacket("A", "B", denomInA, amount, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    }
    ).then(all{
      
      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0),

      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == amount), 
     
      receivePacket("A", "B") 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB2 == amount), 

      //val balanceC = getBalanceIn("C", "charlie", denomBC)
      //assert(balanceC == amount),

    // We don't received the ack yet 
    //  receiveAck("A") 
   // }).then(all{

      // Forwarding Transfer A -> B Completed 
     
      // Forwarding Transfer B to C
      sendPacket("B", "C", denomAB, amount, "forward_account", "charlie",[])
    }
    ).then(all{
      
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), 
     
      receivePacket("B", "C") 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),

      receiveAck("B") 
    }).then(
      receiveAck("A")
    ).then(all{

      // Forwarding Transfer A -> B --> C Completed 
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), 

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),

      // Precondition is met 

      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", denomABC, amount, "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
 
      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == 0),

      // This time token get burned 
      val balanceC = getBalanceIn("C", "escrow_account", denomABC)
      assert(balanceC == 0),
      
      receivePacket("C", "B") 
    }).then(all{
      val balanceB2 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),   

      val balanceC = getBalanceIn("C", "escrow_account", denomABC)
      assert(balanceC == 0),  

      sendPacket("B", "A", denomAB, amount, "forward_account", "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB == 0),

      // This time token get burned
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      failingReceivePacket("B", "A") 
        
    }).then(
      receiveAck("B") // Refund logic should be properly executed on B
    ).then(all{
      val balanceB = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB == 0), // In the case nothing to revert
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), // This should have been reverted to original state before start forwarding transfer. 
      
      //receiveAck("C")
      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),
      
      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 4 Test 

  action initScenario4 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0),"alex" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: []
    })
  }

    run Scenario4Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    pure val denomAB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    
    initScenario4.then(
      // Make sure that charlie has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(all{
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 

      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == amount),
        
      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == 0),
      
      val balanceA3 = getBalanceIn("A", "forward_account", denomInA)
      assert(balanceA3 == 0), 

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB3 == 0), 

      // Start Forwarding Transfer A -> B -> A
      sendPacket("A", "B", denomInA, amount, "alice", "alex",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      
      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0),

      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == amount),

      val balanceA3 = getBalanceIn("A", "forward_account", denomInA)
      assert(balanceA3 == 0),

      // Ok Receive, Apply state changes on B 
      receivePacket("A", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),   

      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0),

      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == amount),

      val balanceA3 = getBalanceIn("A", "forward_account", denomInA)
      assert(balanceA3 == 0),
      
      val balanceA4 = getBalanceIn("A", "alex", denomInA)
      assert(balanceA4 == 0),
      

      sendPacket("B", "A", denomAB, amount, "forward_account", "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB == 0),

      // Tokens get burned here 
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      // Failing Receive, Do not apply state changes on A 
      failingReceivePacket("B", "A") 
        
    }).then(all{
      
      // No Op
      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0), 

      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == amount), 

      val balanceA3 = getBalanceIn("A", "forward_account", denomInA)
      assert(balanceA3 == 0), 

      // Ack on B 
      receiveAck("B") // Refund logic should be properly executed on A
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB3 == 0), 

      //Need to forward back the ack to revert original sendTokens on A 
      forwardAck("B","A") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 

      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == amount), 

      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == 0), // This should have been reverted to original state before start forwarding transfer. 
      
      val balanceA3 = getBalanceIn("A", "forward_account", denomInA)
      assert(balanceA3 == 0), 

      val balanceA4 = getBalanceIn("A", "alex", denomInA)
      assert(balanceA4 == 0),

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB3 == 0), 


      // noop
      chainStates' = chainStates
      }
    )
  }




//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario5 Test 
// Inspiring test from ics20.qnt
//// Test producing a failed acknowledgement:
  //
  // 1. Transfer 50 tokens from Alice on chain A to Bob on chain B.
  // 2. Manipulate the escrow account on chain A, to contain less than 50 tokens.
  //    This will provoke the transfer below to produce a failed acknowledgement.
  // 3. Try to transfer the 50 tokens back from Bob to Alice.
  //    3.1 First, this burns Bob's 50 vouchers on chain B, and sends a packet to chain A.
  //    3.2 Receipt of the packet on chain A calls the `onRecvPacket` callback.
  //    3.3 `onRecvPacket` calls the bank module's `TransferCoins` to unescrow 50 tokens to Alice.
  //    3.4 `TransferCoins` returns an error, because -- after manipulating it in (2) -- the escrow account has insufficient funds.
  //    3.5 The bank module error causes `onRecvPacket` to return a failed acknowledgement.
  //    3.6 `onAcknowledgePacket` on chain "B" re-mints the burned vouchers to Bob.


// Scenario5 Test 
// We want to test C->B->A with an error ack happening on B->A. Thus we want to verify everything get reverted properly 
// In order to create the condition to make the sendFungibleTokens on B->A Pass and then generating an error 
// in the OnRecv, we need to send some tokens to populate the A escrow_account.  
// To this aim we will execute
// 1. A->B 
// 2. B->C. 
// 3. Then we trigger C->B->A
// To checkout the full execution trace run this test with the following command: 
// quint test --main=ics20v2Test ics20v2.qnt --verbosity=3 --match=Scenario1Test
//
  run Scenario5Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    pure val denomAB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomABC = denomAB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomAB.path))
    
    initScenario5.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      // Normal Transfer A to B
      sendPacket("A", "B", ATOM, amount, "alice", "bob",[])
    ).then(
      receivePacket("A", "B") 
    ).then(
      receiveAck("A") 
    ).then(all{
      
      // alice balance should be 0 
      val balanceA = getBalanceIn("A", "alice", denomInA)
      assert(balanceA == 0), 
      // escrow_account on A should be amount  
      val balanceA2 = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA2 == amount), 
       // bob balance on B should B amount
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == amount), 

      // Normal Transfer B to C
      sendPacket("B", "C", denomAB, amount, "bob", "charlie",[])
    }).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B") 
    ).then(all{
      // Again same checks on B and C 
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 
      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount),


      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", denomABC, amount, "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      receivePacket("C", "B") 
    }).then(all{
      // forward_account on B should be amount // HERE ARE TOKEN TRANSFERRED FROM escrow_account to forward_account? 
      // OR ARE TOKENS MINTED ON FORWARD ACCOUNT? 
      val balanceB2 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0), 
      // Manipulate Escrow Balance on Chain A. This should be sufficient to make the transfer from B -> A succed
      // And the onRecv function on A to generate an error ack.       
      setBalanceIn("A", "escrow_account", ATOM, amount-1)  
    }).then(
      // The sendFungibleTokens here must succed  
      sendPacket("B", "A", denomAB, amount, "forward_account", "alice",[])
    ).then(all{
      
      val balanceB = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB == 0),
      //val balanceA = getBalanceIn("A", "alice", denomABC)
      //assert(balanceA == amount),
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      receivePacket("B", "A") // This fails because sendPacket failed as depicted in the scenario1. 
        
    }).then(
      receiveAck("B") // Error ack is properly written here. // Refund logic properly executed on B
    ).then(all{
      val balanceB = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB == 0), // In the case nothing to revert
      
      val balanceB = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {
      // check that voucher exists on chain B
      //val balanceB = getBalanceIn("B", "escrow_account", denomSentFromAToB)
      //assert(balanceB == amount),
      // check that the balance is updated on chainC
      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),

      // check that balance on chain B is empty
      //val balanceB = getBalanceIn("B", "bob", denomSentFromAToB)
      //assert(balanceB == 0),
      //check the escrow_account balance on chain B is amount
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == amount),

      // check that balance on chain A is empty
      //val balanceA = getBalanceIn("A", "alice", denomInA)
      //assert(balanceA == 0),
      // check the escrow_account balance on chain A is amount
      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == 89),

      // noop
      chainStates' = chainStates
      }
    )
  }


}
