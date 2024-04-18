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
    pure val channelForwardingAddress= assignCFA("escrow_account", chainState, packet)
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
      // if the transfer failed, refund the tokens
      pure val tempChainState = eventuallyRefund(chainState, packet, acknowledgement)
      
      // check if the packet that was sent is from a previously forwarded packet
      if(tempChainState.forwardedPacket!=[]){
          pure val prevPacket=tempChainState.forwardedPacket.head() 
          if (acknowledgement.success) {
              // The acknowledgment get written in the action for simuliation purposes. 
              //pure val ack ={ success: true, errorMessage: "forwarded packet succeeded", packet: prevPacket }
              //val newInAcknowledgements = tempChainState.inAcknowledgements.union(Set(ack))
              //pure val newChainState= tempChainState.with("inAcknowledgements", newInAcknowledgements)
              tempChainState
          } else {
                // the forwarded packet has failed, thus the funds have been refunded to the forwarding address.
                // we must revert the changes that came from successfully receiving the tokens on our chain
                // before propogating the error acknowledgement back to original sender chain        
                pure val revertedChainState=revertInFlightChanges(tempChainState,packet,prevPacket)
                // The acknowledgment get written in the action for simuliation purposes.
                // write error acknowledgement
                //pure val ack ={ success: false, errorMessage: "forwarded packet failed", packet: prevPacket }
                //val newInAcknowledgements = revertedChainState.inAcknowledgements.union(Set(ack))
                //pure val newChainState= revertedChainState.with("inAcknowledgements", newInAcknowledgements)
                revertedChainState
                  }
      }else tempChainState  
  }

  /// Called by the routing module when a packet sent by this module has timed out
  /// (such that it will not be received on the destination chain).
  pure def onTimeoutPacket(chainState: ChainState, packet: Packet): (ChainState)  = {
    // the packet timed out, so refund the tokens
    pure val refundChainState=refundTokens(chainState, packet)
    // check if the packet was sent is from a previously forwarded packet
    pure val prevPacket=refundChainState.forwardedPacket.head()
    if(refundChainState.forwardedPacket!=[]){
      // the forwarded packet has failed, thus the funds have been refunded to the forwarding address.
      // we must revert the changes that came from successfully receiving the tokens on our chain
      // before propogating the error acknowledgement back to original sender chain
      pure val tempChainState=revertInFlightChanges(refundChainState,packet,prevPacket)
      // write error acknowledgement
      // The acknowledgment get written in the action for simuliation purposes.
      //pure val ack ={ success: false, errorMessage: "forwarded packet failed", packet: prevPacket }
      //val newInAcknowledgements = tempChainState.inAcknowledgements.union(Set(ack))
      //pure val newChainState= tempChainState.with("inAcknowledgements", newInAcknowledgements)
      tempChainState
      }
      else refundChainState
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
          // check if the packet we received was a source token for our chain
          if (movingBackAlongTrace(receivedPacket.data.denom, hopElementRecv)) {
              // receive sent tokens from the received escrow to the forward escrow account
              // so we must send the tokens back from the forward escrow to the original received escrow account
              chainState.bank.TransferCoins(forwardEscrow, reverseEscrow, sentPacket.data.denom, sentPacket.data.amount)
          }
          else {
              // receive minted vouchers and sent to the forward escrow account
              // so we must remove the vouchers from the forward escrow account and burn them
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
            // No Op Miniting 0 Tokens 
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
  // NEED TO CHANGE CHANNEL_TOPOLOGY FOR FORWARDING TEST
  pure val CHANNEL_TOPOLOGY = Map(
    "A" -> Map(
      "B" -> "channelToB"
      //"C" -> "channelToC"
    ),
    "B" -> Map(
      "A" -> "channelToA",
      "C" -> "channelToC"
    ),
    "C" -> Map(
      //"A" -> "channelToA",
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
      val newInAcknowledgements = ackedChainState.inAcknowledgements.exclude(Set(acknowledgement))
      // remove `acknowledgement.packet` from receivedButUnacknowledgedPackets
      
      val newInUnackPackets = ackedChainState.receivedButUnacknowledgedPackets.exclude(Set(acknowledgement.packet))
      
      val newChainState = ackedChainState.with("inAcknowledgements", newInAcknowledgements)
                                         .with("receivedButUnacknowledgedPackets", newInUnackPackets)

      // (3) Quint state transition:
      chainStates' = chainStates.set(chain, newChainState)
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
  action init = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT), 
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

run DetailedHappyPathTest = {
    pure val amount = 90

    // NOTE: fungible token is prefixed with the full trace in order to verify the packet commitment
    pure val denomInA = ATOM
    pure val denomSentFromAToB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomSentFromBToC = denomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomSentFromAToB.path))
    init.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      sendPacket("A", "B", ATOM, amount, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(
      receivePacket("A", "B") 
    ).then(
      sendPacket("B", "C", denomSentFromAToB, amount, "escrow_account", "charlie",[])
    ).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B")
    ).then(
      receiveAck("A")
    ).then(all {
      // check that voucher exists on chain B
      val balanceB = getBalanceIn("B", "escrow_account", denomSentFromAToB)
      assert(balanceB == amount),
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

  // Tansfer happening from A to C using the forwarding path and the sendTransfer previously described. 
  // In quint we need to call twice the sendTransfer to appreciate the state changes.  
  run HappyPathTest = {
    pure val amount = 90

    // NOTE: fungible token is prefixed with the full trace in order to verify the packet commitment
    pure val denomInA = ATOM
    pure val denomSentFromAToB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomSentFromBToC = denomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomSentFromAToB.path))
    init.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      sendTransfer("A", "B", ATOM, amount, "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(all {
      // check that voucher exists on chain B
      val balanceB = getBalanceIn("B", "escrow_account", denomSentFromAToB)
      assert(balanceB == amount),

      sendTransfer("B", "C", denomSentFromAToB, amount, "escrow_account", "charlie",[])
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
        // send from chainC back to chainB
       //sendTransfer("C", "B", denomSentFromBToC, amount, "charlie", "bob",[])
      }
    )
  }




}
