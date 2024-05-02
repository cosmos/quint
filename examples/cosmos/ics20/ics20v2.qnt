// -*- mode: Bluespec; -*-

/**
 * The ics20v2 specification is an extension of the ics20 with support for multidenom and token forwarding functionalities. 
 * Many thanks to our colleagues Gabriela Moreira and Thomas Pani, Informal Systems, 2023 
 * for providing the ground base of this spec with the implementation of bank.qnt, base.qnt, denomTrace.qnt and ics20.qnt. 
 *   
 * Stefano Angieri, Carlos Rodriguez, Aditya Sripal, Interchain Foundation, 2024
 * 
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

  // Ics20v2 types  
 
  type Token = {
  denom: DenomTrace,
  //trace: str, contained in DenomTrace which has baseDenom and Path   
  amount: UINT256 
  }

  type FungibleTokenData= {
    tokens: List[Token], 
    sender: Address,
    receiver: Address,
    memo: str,
    forwardingPath: ForwardingPath
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

  type ChainState = {
    bank: Accounts,
    channels: ChannelCounterparties,
    channelEscrowAddresses: Channel -> Address,
    channelForwardingAddresses: Channel -> Address, 
    // IBC packet handling:
    outPackets: Set[Packet],                        // outgoing unreceived packets
    receivedButUnacknowledgedPackets: Set[Packet],  // received but unacknowledged packets
    inAcknowledgements: Set[FungibleTokenPacketAcknowledgement],  // incoming acknowledgements
    inTimeouts: Set[Packet], // incoming timeouts
    forwardedPacket: List[Packet], //packetForwardPath                                
    receivedTokens: List[Token],
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

// Helper function to navigate the token list for multidenom support 
  pure def getNextToken(Tokens: List[Token]): (DenomTrace, UINT256, List[Token]) = {
    pure val headElement = Tokens.head()  // Get the first element
    pure val nextDenom  = headElement.denom   // Get nextDenom
    pure val nextAmount = headElement.amount   // Get nextAmount
    pure val newTokenList= Tokens.tail() // Delete first element of the Token list 
    (nextDenom,nextAmount,newTokenList)

  }

// SendFungibleTokensV2 supporting multidenom and token forwarding
// To model multidenom we will use 3 as an upper bound on the number of tokens that can be forwarded in a single tx. 
// SendFungibleTokensV2 supports multidenom and token forwarding, using three tokens as the testing 
// upper limit per transaction. This number allows us to comprehensively address all potential 
// error scenarios—beginning, middle, or end of the transaction sequence. 
// We model errors within these critical points using a small, manageable set of tokens (0, 1, 2), 
// ensuring our system's logic is robust against errors in larger sequences. 
// This approach leverages the principle that larger sets of tokens can be considered as combinations of 
// smaller sets, such as viewing a set of four tokens as a sum of one token and three tokens. 
// By proving the system's reliability in handling three tokens effectively, 
// we can infer its correct behavior for any number of tokens due to the predictable, 
// systematic nature of error handling and transaction processes.
// 
// To ensure atomicity execution, we work on the token list without using fold function.

 pure def sendFungibleTokens(chainState: ChainState, tokens012: List[Token], 
                              sender: Address, receiver: Address, forwardingPath: ForwardingPath, sourcePort: str, sourceChannel: Channel,
                              timeoutHeight: Height, timeoutTimestamp: uint64): ChainState = {
      
      // Compute First Step Bank Result results is a tuple, bankResult and chainState
      pure val bankResult0 = 

          if(tokens012!=[]){
            pure val token0= getNextToken(tokens012)
            pure val denom0 = token0._1
            pure val amount0 = token0._2
          
            if (movingBackAlongTrace(denom0, { port: sourcePort, channel: sourceChannel })) {
              // burn vouchers
              pure val res=chainState.bank.BurnCoins(sender, denom0, amount0) 
              (res, chainState.with("bank",res.accounts))
            } else {
              // escrow tokens
              pure val escrowAccount = chainState.channelEscrowAddresses.get(sourceChannel)
              pure val res=chainState.bank.TransferCoins(sender, escrowAccount, denom0, amount0) 
               (res, chainState.with("bank",res.accounts))
              
              } 
          }
          // No Token to forward
          else {({success: false, accounts: chainState.bank}, chainState)}
      
      // Retrieve remaining token list elements
      pure val tokens12 = {      
         if(tokens012!=[]){
         pure val token12= getNextToken(tokens012)
         token12._3
         } else []
      }

    // Compute Middle Step Bank Result
      pure val bankResult1 = 
        if (bankResult0._1.success and tokens12!=[]) {
            pure val token1= getNextToken(tokens12)
            pure val denom1 = token1._1
            pure val amount1 = token1._2

          if (movingBackAlongTrace(denom1, { port: sourcePort, channel: sourceChannel })) {
              // burn vouchers
              //(chainStateV2.bank).BurnCoins(sender, denom1, amount1)
              pure val res=bankResult0._2.bank.BurnCoins(sender, denom1, amount1) 
               (res, chainState.with("bank",res.accounts))
              
              } else {
                // escrow tokens
                pure val escrowAccount = chainState.channelEscrowAddresses.get(sourceChannel)
                pure val res= bankResult0._2.bank.TransferCoins(sender, escrowAccount, denom1, amount1)
                (res, chainState.with("bank",res.accounts))
              }
          }
          // If no more tokens to forward, propagate the previous bank result. 
          // If there was an error in the first step propagate the first bank result error. 
          else bankResult0

        // Retrieve remaining token list elements
      pure val tokens2 = {      
         if(tokens12!=[]){
         pure val token2= getNextToken(tokens12)
         token2._3
         } else []
      }

    // Compute Last Step Bank Result
    pure val finalBankResult = 
        
        if (bankResult1._1.success and tokens2!=[]) {
        pure val token2= getNextToken(tokens2)
        pure val denom2 = token2._1
        pure val amount2 = token2._2
        
        if (movingBackAlongTrace(denom2, { port: sourcePort, channel: sourceChannel })) {
              // burn vouchers
              pure val res= (bankResult1._2.bank).BurnCoins(sender, denom2, amount2)
              (res, chainState.with("bank",res.accounts))
              } else {
                // escrow tokens
                pure val escrowAccount = chainState.channelEscrowAddresses.get(sourceChannel)
                pure val res=bankResult1._2.bank.TransferCoins(sender, escrowAccount, denom2, amount2)
                (res, chainState.with("bank",res.accounts))
              }
        }
        // If no more token to forward and previous result == success --> propagate the middle step result
        else if (bankResult1._1.success) bankResult1
        // Otherwise propagate the bankResult 0
              else bankResult0 

// Logic :: If bankResult0 == False --> bankResult1 == bankResult2 == bankResult0 False by construction. 
// Logic :: If bankResult1 == False --> bankResult2 == False by construction.  
    
    
    if (finalBankResult._1.success) {

      // Manipulate Data to be V2 data 
      pure val data = { tokens: tokens012, sender: sender, receiver: receiver, memo: "", forwardingPath: forwardingPath }

      // handler.sendPacket
      pure val packetV2 = {
        data: data,
        sourcePort: sourcePort,
        sourceChannel: sourceChannel,
        destPort: "transfer",
        destChannel: getCounterparty(chainState, sourceChannel),
      }

      chainState.with("bank", finalBankResult._1.accounts)
                  .with("outPackets", chainState.outPackets.union(Set(packetV2)))
    
  }
  else {
    chainState
  }
  }

// Helper functions for onRecvPacket Logic execution
  pure def assignCFA(address: Address, chainState: ChainState, packet: Packet): str = {
    if(chainState.channelForwardingAddresses.get(packet.destChannel)==""){
        (address) // Pass in MOCK ADDRESS or WRITE NEW ADDRESS FUNCTION  
    }else (chainState.channelForwardingAddresses.get(packet.destChannel))   
    }

  /// Gets the `forward_account` a or c for the chain B.
  def getForwardAccount(channel) = {
    if(channel=="channelToC") "forward_account_c"
    else "forward_account_a"
    
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
    pure val tokens012= data.tokens
    pure val address= getForwardAccount(packet.destChannel)
    // Addresses assignment. Helper functions define spec logic for assignment 
    pure val channelForwardingAddress= assignCFA(address, chainState, packet)
    pure val addressTuple=assignRecvAddress(data.forwardingPath!=[],packet, channelForwardingAddress)
    pure val receiver = addressTuple._1
    pure val finalReceiver = addressTuple._2 
    
    // Note that for quint is better not the preconstruct a succesfull ack 
    // but rather to assign it to true of false when needed
    
    // Compute First Step Bank Result
      pure val bankResult0 = 
          if(tokens012!=[]){
            pure val token0= getNextToken(tokens012)
            pure val denom0 = token0._1
            pure val amount0 = token0._2
            
            // HERE PLAY WITH MULTIDENOM LOGIC 
            pure val movingBack = movingBackAlongTrace(denom0, { port: packet.sourcePort, channel: packet.sourceChannel })
            pure val newDenom = updateTrace(movingBack, denom0, { port: packet.destPort, channel: packet.destChannel })

            // result is a pair of 1. a BankResult and 2. an error message that is used in case BankResult.success = false
            if (movingBack) {
            // unescrow tokens to receiver
            pure val escrowAccount = chainState.channelEscrowAddresses.get(packet.destChannel)
            pure val bankResult = chainState.bank.TransferCoins(escrowAccount, receiver, newDenom, amount0)  
            pure val receivedTokens= [{denom: denom0, amount: amount0}]
            pure val newChainState = chainState.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
            (bankResult, "transfer coins failed",newChainState )
            } else {
                // mint vouchers to receiver
                pure val bankResult = chainState.bank.MintCoins(receiver, newDenom, amount0)
                pure val receivedTokens= [{denom: denom0, amount: amount0}]
                pure val newChainState = chainState.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
                (bankResult, "mint coins failed",newChainState)
              }
            } else {
              // No Token to receive
              pure val bankResult = {success: false, accounts: chainState.bank}
              (bankResult, "receive failed",chainState) 
            }
      //pure val bankResult0 = Result0._1
      // Retrieve remaining token list elements
      pure val tokens12 = {      
         if(tokens012!=[]){
         pure val token12= getNextToken(tokens012)
         token12._3
         } else []
      }

    // Compute Middle Step Bank Result
      pure val bankResult1 = 
        if (bankResult0._1.success and tokens12!=[]) {
            pure val token1= getNextToken(tokens12)
            pure val denom1 = token1._1
            pure val amount1 = token1._2
            
            // HERE PLAY WITH MULTIDENOM LOGIC 
            pure val movingBack = movingBackAlongTrace(denom1, { port: packet.sourcePort, channel: packet.sourceChannel })
            pure val newDenom = updateTrace(movingBack, denom1, { port: packet.destPort, channel: packet.destChannel })

            // result is a pair of 1. a BankResult and 2. an error message that is used in case BankResult.success = false
            if (movingBack) {
            pure val escrowAccount = bankResult0._3.channelEscrowAddresses.get(packet.destChannel)
            pure val bankResult = bankResult0._3.bank.TransferCoins(escrowAccount, receiver, newDenom, amount1)  
            pure val receivedTokens= bankResult0._3.receivedTokens.append({denom: denom1, amount: amount1})
            pure val newChainState = bankResult0._3.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
            
            (bankResult, "transfer coins failed", newChainState)
            } else {
                // mint vouchers to receiver
                pure val bankResult = bankResult0._3.bank.MintCoins(receiver, newDenom, amount1)
                pure val receivedTokens= bankResult0._3.receivedTokens.append({denom: denom1, amount: amount1})
                pure val newChainState = bankResult0._3.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
                (bankResult, "mint coins failed", newChainState)
              }
            } 
          // If no more tokens to receive, propagate the previous bank result. 
          // If there was an error in the first step propagate the first bank result error. 
          else bankResult0

        // Retrieve remaining token list elements
      pure val tokens2 = {      
         if(tokens12!=[]){
         pure val token2= getNextToken(tokens12)
         token2._3
         } else []
      }

    // Compute Last Step Bank Result
    pure val finalBankResult = 
        
        if (bankResult1._1.success and tokens2!=[]) {
        pure val token2= getNextToken(tokens2)
        pure val denom2 = token2._1
        pure val amount2 = token2._2

        pure val movingBack = movingBackAlongTrace(denom2, { port: packet.sourcePort, channel: packet.sourceChannel })
        pure val newDenom = updateTrace(movingBack, denom2, { port: packet.destPort, channel: packet.destChannel })

        // result is a pair of 1. a BankResult and 2. an error message that is used in case BankResult.success = false
        if (movingBack) {
        // unescrow tokens to receiver
          pure val escrowAccount = bankResult1._3.channelEscrowAddresses.get(packet.destChannel)
          pure val bankResult = bankResult1._3.bank.TransferCoins(escrowAccount, receiver, newDenom, amount2)  
          pure val receivedTokens= bankResult1._3.receivedTokens.append({denom: denom2, amount: amount2})
          pure val newChainState = bankResult1._3.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
          (bankResult, "transfer coins failed", newChainState)
          } else {
            // mint vouchers to receiver
            pure val bankResult = bankResult1._3.bank.MintCoins(receiver, newDenom, amount2)
            pure val receivedTokens= bankResult1._3.receivedTokens.append({denom: denom2, amount: amount2})
            pure val newChainState = bankResult1._3.with("bank",bankResult.accounts)
                                                .with("receivedTokens",receivedTokens)
                (bankResult, "mint coins failed",newChainState)
              }
            }  
       
        // If no more token to forward and previous result == success --> propagate the middle step result
        else if (bankResult1._1.success) bankResult1
        // Otherwise propagate the bankResult 0
              else bankResult0 

    
    pure val ack = if (finalBankResult._1.success) {
      { success: true, errorMessage: "", packet: packet }
    } else {
      { success: false, errorMessage: finalBankResult._2, packet: packet }
    }


    if(ack.success==false){
      (chainState,ack)
    }
    // Otherwise proceed with token forwarding logic. 
    else {
      if(data.forwardingPath!=[]){

        pure val tempChainState = chainState.with("bank", finalBankResult._1.accounts)
                                            
        pure val nextStuff=getNextPortChannel(data.forwardingPath)
        pure val nextPort=nextStuff._1
        pure val nextChannel=nextStuff._2
        pure val newForwardingPath=nextStuff._3

        pure val newTempChainState = sendFungibleTokens(tempChainState, data.tokens, 
                              receiver, finalReceiver, newForwardingPath, nextPort, nextChannel,
                              10,10) // Which Timeout?  
        // store packet for future sending ack
        pure val newChainState = newTempChainState.with("forwardedPacket", [packet])
        (newChainState,ack)
      }
        else{
        
        pure val tempChainState = chainState.with("bank", finalBankResult._1.accounts)
                                            
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
  // RefundTokensV2 with multidenom and token forwarding 
    pure def refundTokens(chainState: ChainState, packet: Packet): ChainState = {
    pure val data: FungibleTokenData = packet.data
    pure val tokens012 = data.tokens
      
      // Compute First Step Bank Result results is a tuple, bankResult and chainState
      pure val bankResult0 = 

          if(tokens012!=[]){
            pure val token0= getNextToken(tokens012)
            pure val denom0 = token0._1
            pure val amount0 = token0._2
          
           pure val source: HopElement = { port: packet.sourcePort, channel: packet.sourceChannel }
            if (movingBackAlongTrace(denom0, source)) {
            // The (failed) transfer attempt was moving the token back along its denom trace.
            // For this, we originally burnt vouchers in `sendFungibleTokens`, so mint them back.
            pure val res=chainState.bank.MintCoins(data.sender, denom0, amount0)
            (res, chainState.with("bank",res.accounts))
            
            } else {
            // The (failed) transfer attempt was moving the token further along its denom trace.
            // For this, we originally escrowed tokens in `sendFungibleTokens`, so unescrow them back.
            pure val escrowAccount = chainState.channelEscrowAddresses.get(packet.sourceChannel)
            pure val res=chainState.bank.TransferCoins(escrowAccount, data.sender, denom0, amount0)
            (res, chainState.with("bank",res.accounts))
            }
          
          } 
          // No Token to refund
         else {({success: false, accounts: chainState.bank}, chainState)}
      
      // Retrieve remaining token list elements
      pure val tokens12 = {      
         if(tokens012!=[]){
         pure val token12= getNextToken(tokens012)
         token12._3
         } else []
      }

    // Compute Middle Step Bank Result
      pure val bankResult1 = 
        if (bankResult0._1.success and tokens12!=[]) {
            pure val token1= getNextToken(tokens12)
            pure val denom1 = token1._1
            pure val amount1 = token1._2
            pure val source: HopElement = { port: packet.sourcePort, channel: packet.sourceChannel }
            if (movingBackAlongTrace(denom1, source)) {
            // The (failed) transfer attempt was moving the token back along its denom trace.
            // For this, we originally burnt vouchers in `sendFungibleTokens`, so mint them back.
            pure val res=bankResult0._2.bank.MintCoins(data.sender, denom1, amount1)
            (res, bankResult0._2.with("bank",res.accounts))
            } else {
            // The (failed) transfer attempt was moving the token further along its denom trace.
            // For this, we originally escrowed tokens in `sendFungibleTokens`, so unescrow them back.
            pure val escrowAccount = bankResult0._2.channelEscrowAddresses.get(packet.sourceChannel)
            pure val res=bankResult0._2.bank.TransferCoins(escrowAccount, data.sender, denom1, amount1)
            (res, bankResult0._2.with("bank",res.accounts))
            }
          }
          // If no more tokens to forward, propagate the previous bank result. 
          // If there was an error in the first step propagate the first bank result error. 
          else bankResult0

        // Retrieve remaining token list elements
      pure val tokens2 = {      
         if(tokens12!=[]){
         pure val token2= getNextToken(tokens12)
         token2._3
         } else []
      }

    // Compute Last Step Bank Result
    pure val finalBankResult = 
        
        if (bankResult1._1.success and tokens2!=[]) {
        pure val token2= getNextToken(tokens2)
        pure val denom2 = token2._1
        pure val amount2 = token2._2
        pure val source: HopElement = { port: packet.sourcePort, channel: packet.sourceChannel }
        if (movingBackAlongTrace(denom2, source)) {
            // The (failed) transfer attempt was moving the token back along its denom trace.
            // For this, we originally burnt vouchers in `sendFungibleTokens`, so mint them back.
            pure val res=bankResult1._2.bank.MintCoins(data.sender, denom2, amount2)
            (res, bankResult1._2.with("bank",res.accounts))
            } else {
            // The (failed) transfer attempt was moving the token further along its denom trace.
            // For this, we originally escrowed tokens in `sendFungibleTokens`, so unescrow them back.
            pure val escrowAccount = bankResult1._2.channelEscrowAddresses.get(packet.sourceChannel)
            pure val res=bankResult1._2.bank.TransferCoins(escrowAccount, data.sender, denom2, amount2)
            (res, bankResult1._2.with("bank",res.accounts))
            }
        }
        // If no more token to forward and previous result == success --> propagate the middle step result
        else if (bankResult1._1.success) bankResult1
        // Otherwise propagate the bankResult 0
              else bankResult0 

// Logic :: If bankResult0 == False --> bankResult1 == bankResult2 == bankResult0 False by construction. 
// Logic :: If bankResult1 == False --> bankResult2 == False by construction.  
    
    if (finalBankResult._1.success) {
      chainState.with("bank", finalBankResult._1.accounts)
    } else {
      // TODO: ICS 20 does not specify what happens if the bank modules return an error.
      //       We treat bank failure as a noop.
      chainState
    }
  }


  /// Called by the routing module when a packet sent by this module has been acknowledged.
  pure def onAcknowledgePacket(chainState: ChainState, packet: Packet,
                               acknowledgement: FungibleTokenPacketAcknowledgement) : (ChainState) = {
      
      // check if the packet that was sent is from a previously forwarded packet
      if(chainState.forwardedPacket!=[]){
          pure val prevPacket=chainState.forwardedPacket.head() 
          if (acknowledgement.success) {
              // No Op 
              chainState
          } else {
                // the forwarded packet has failed, thus the funds have been refunded to the forwarding address.
                // we must revert the changes that came from successfully receiving the tokens on our chain
                // before propogating the error acknowledgement back to original sender chain        
                pure val revertedChainState=revertInFlightChanges(chainState,packet,prevPacket)
                revertedChainState
                }
      }else {
        // if the transfer failed, refund the tokens
      if (acknowledgement.success==false) {
       pure val newChainState= refundTokens(chainState, packet)
      newChainState 
      }else chainState
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
//******* IMPORTANT - note that movingBackAlongTrace returns the opposite of isSource defined in the spec ******* 
pure def revertInFlightChanges(chainState: ChainState, sentPacket: Packet, receivedPacket: Packet): ChainState = {
 pure val forwardEscrow = chainState.channelEscrowAddresses.get(sentPacket.sourceChannel)
 pure val reverseEscrow = chainState.channelEscrowAddresses.get(receivedPacket.destChannel)
 pure val hopElementSent = {port: sentPacket.sourcePort, channel: sentPacket.sourceChannel}
 pure val hopElementRecv = {port: receivedPacket.destPort, channel: receivedPacket.destChannel}
 pure val tokens012=sentPacket.data.tokens

      pure val bankResult0 = 

          if(tokens012!=[]){
            pure val token0= getNextToken(tokens012)
            pure val denom0 = token0._1
            pure val amount0 = token0._2
          
      // check if the packet we sent out was sending as source or not
      // in this case we escrowed the outgoing tokens
      if (movingBackAlongTrace(denom0, hopElementSent)==false) {
          // check if the packet we received was a source token for our chain
          if (movingBackAlongTrace(denom0, hopElementRecv)==false) {
              // receive sent tokens from the received escrow to the forward escrow account
              // so we must send the tokens back from the forward escrow to the original received escrow account
              pure val res= chainState.bank.TransferCoins(forwardEscrow, reverseEscrow, denom0, amount0)
              (res, chainState.with("bank",res.accounts))
            
          }
          else {
              // receive minted vouchers and sent to the forward escrow account
              // so we must remove the vouchers from the forward escrow account and burn them
              pure val res= chainState.bank.BurnCoins(forwardEscrow, denom0, amount0)
              (res, chainState.with("bank",res.accounts))
            
            }
    } else {
          // in this case we burned the vouchers of the outgoing packets
          // check if the packet we received was a source token for our chain
          // in this case, the tokens were unescrowed from the reverse escrow account
          if (movingBackAlongTrace(denom0, hopElementRecv)==false){
            // in this case we must mint the burned vouchers and send them back to the escrow account
            pure val res= chainState.bank.MintCoins(reverseEscrow, denom0, amount0)
            (res, chainState.with("bank",res.accounts))
            
          }else{
            // if it wasn't a source token on receive, then we simply had minted vouchers and burned them in the receive.
            // So no state changes were made, and thus no reversion is necessary
            // No Op Miniting 0 Tokens 
            pure val res = chainState.bank.MintCoins(reverseEscrow, denom0, 0)
            (res, chainState.with("bank",res.accounts))
            
            }
          }
          } 
          // No Token to refund
         else {({success: false, accounts: chainState.bank}, chainState)}
      
      // Retrieve remaining token list elements
      pure val tokens12 = {      
         if(tokens012!=[]){
         pure val token12= getNextToken(tokens012)
         token12._3
         } else []
      }

    // Compute Middle Step Bank Result
      pure val bankResult1 = 
        if (bankResult0._1.success and tokens12!=[]) {
            pure val token1= getNextToken(tokens12)
            pure val denom1 = token1._1
            pure val amount1 = token1._2      
            
      // check if the packet we sent out was sending as source or not
      // in this case we escrowed the outgoing tokens
      if (movingBackAlongTrace(denom1, hopElementSent)==false) {
          // check if the packet we received was a source token for our chain
          if (movingBackAlongTrace(denom1, hopElementRecv)==false) {
              // receive sent tokens from the received escrow to the forward escrow account
              // so we must send the tokens back from the forward escrow to the original received escrow account
              pure val res= bankResult0._2.bank.TransferCoins(forwardEscrow, reverseEscrow, denom1, amount1)
              (res, bankResult0._2.with("bank",res.accounts))
            
          }
          else {
              // receive minted vouchers and sent to the forward escrow account
              // so we must remove the vouchers from the forward escrow account and burn them
              pure val res= bankResult0._2.bank.BurnCoins(forwardEscrow, denom1, amount1)
              (res, bankResult0._2.with("bank",res.accounts))
            
            }
    } else {
          // in this case we burned the vouchers of the outgoing packets
          // check if the packet we received was a source token for our chain
          // in this case, the tokens were unescrowed from the reverse escrow account
          if (movingBackAlongTrace(denom1, hopElementRecv)==false){
            // in this case we must mint the burned vouchers and send them back to the escrow account
            pure val res= bankResult0._2.bank.MintCoins(reverseEscrow, denom1, amount1)
            (res, bankResult0._2.with("bank",res.accounts))
            
          }else{
            // if it wasn't a source token on receive, then we simply had minted vouchers and burned them in the receive.
            // So no state changes were made, and thus no reversion is necessary
            // No Op Miniting 0 Tokens 
            pure val res = bankResult0._2.bank.MintCoins(reverseEscrow, denom1, 0)
            (res, bankResult0._2.with("bank",res.accounts))
            
            }
          }
          } 
          // If no more tokens to revert, propagate the previous bank result. 
          // If there was an error in the first step propagate the first bank result error. 
          else bankResult0

        // Retrieve remaining token list elements
      pure val tokens2 = {      
         if(tokens12!=[]){
         pure val token2= getNextToken(tokens12)
         token2._3
         } else []
      }

    // Compute Last Step Bank Result
    pure val finalBankResult = 
        
        if (bankResult1._1.success and tokens2!=[]) {
        pure val token2= getNextToken(tokens2)
        pure val denom2 = token2._1
        pure val amount2 = token2._2
        
      // check if the packet we sent out was sending as source or not
      // in this case we escrowed the outgoing tokens
      if (movingBackAlongTrace(denom2, hopElementSent)==false) {
          // check if the packet we received was a source token for our chain
          if (movingBackAlongTrace(denom2, hopElementRecv)==false) {
              // receive sent tokens from the received escrow to the forward escrow account
              // so we must send the tokens back from the forward escrow to the original received escrow account
              pure val res= bankResult1._2.bank.TransferCoins(forwardEscrow, reverseEscrow, denom2, amount2)
              (res, bankResult1._2.with("bank",res.accounts))
            
          }
          else {
              // receive minted vouchers and sent to the forward escrow account
              // so we must remove the vouchers from the forward escrow account and burn them
              pure val res= bankResult1._2.bank.BurnCoins(forwardEscrow, denom2, amount2)
              (res, bankResult1._2.with("bank",res.accounts))
            
            }
    } else {
          // in this case we burned the vouchers of the outgoing packets
          // check if the packet we received was a source token for our chain
          // in this case, the tokens were unescrowed from the reverse escrow account
          if (movingBackAlongTrace(denom2, hopElementRecv)==false){
            // in this case we must mint the burned vouchers and send them back to the escrow account
            pure val res= bankResult1._2.bank.MintCoins(reverseEscrow, denom2, amount2)
            (res, bankResult1._2.with("bank",res.accounts))
            
          }else{
            // if it wasn't a source token on receive, then we simply had minted vouchers and burned them in the receive.
            // So no state changes were made, and thus no reversion is necessary
            // No Op Miniting 0 Tokens 
            pure val res = bankResult1._2.bank.MintCoins(reverseEscrow, denom2, 0)
            (res, bankResult0._2.with("bank",res.accounts))
            
            }
          }
          } 
        // If no more token to forward and previous result == success --> propagate the middle step result
        else if (bankResult1._1.success) bankResult1
        // Otherwise propagate the bankResult 0
              else bankResult0 

// Logic :: If bankResult0 == False --> bankResult1 == bankResult2 == bankResult0 False by construction. 
// Logic :: If bankResult1 == False --> bankResult2 == False by construction.  
    
    if (finalBankResult._1.success) {
      chainState.with("bank", finalBankResult._1.accounts)
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
  //  For testing, imagine the following topology between channels in chains A, B and C.
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


/// Gets the `escrow_account` a or c for the chain B.
  def getEscrowAccount(channel) = {
    if(channel=="channelToC") "escrow_account_c"
    else "escrow_account_a"
    
  }



  /// Send a packet from `sourceChain` to `destChain`, indicating a transfer
  /// of `amount`-many tokens of `denom` from `sender` to `receiver`.
action sendPacket(sourceChain: str, destChain: str, tokens: List[Token],
                    sender: Address, receiver: Address, forwardingPath: ForwardingPath): bool = all {
    // (1) Pre-condition:
    // there is a channel between `sourceChain` and `destChain`
    hasChannelBetween(sourceChain, destChain),

    // Extract Forwarding Path 
    // (2) Send the packet using `sendFungibleTokens`:
    val sourceChainState = chainStates.get(sourceChain)
    val newSourceChainState = sendFungibleTokens(sourceChainState, tokens,
                                                 sender, receiver, forwardingPath, 
                                                 "transfer", CHANNEL_TOPOLOGY.get(sourceChain).get(destChain),
                                                 0, 0)
    // (3) Quint state transition:
    chainStates' = chainStates.set(sourceChain, newSourceChainState)
  }


  // Mock Function to generate an error during the receive 
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
// Receive packet v2
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
        val newReceivedTokens = packet.data.tokens
        
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

 
  // Mock Function to forward the correct error ack. Useful to trigger error onAck logic.  
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
  pure val OSMO = toDenom("osmo")
  pure val ETH = toDenom("eth")
  pure val USER_ACCOUNTS = Set("alice", "bob", "charlie")
  pure val ESCROW_ACCOUNT = "escrow_account"

  // Initialize the protocol
  // this init function must be defined to run the simulator. 
  action init = {
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
      forwardedPacket: [],
      receivedTokens: []
    })
  }

  // Take a step in the protocol (non-deterministically chooses one action).
  action step = {
    pure val token=[{denom: ATOM, amount: oneOf(1.to(10))}]
    nondet sourceChain = CHAINS.oneOf()
    nondet destChain = CHAINS.exclude(Set(sourceChain)).oneOf()
    any {
      //nondet amount = oneOf(1.to(10))
      nondet sourceAddr = USER_ACCOUNTS.oneOf()
      nondet destAddr = USER_ACCOUNTS.exclude(Set(sourceAddr)).oneOf()
      sendPacket(sourceChain, destChain, token, sourceAddr, destAddr,[]),
      receivePacket(sourceChain, destChain),
      timeoutPacket(sourceChain, destChain),
      receiveAck(sourceChain),
      failingReceivePacket(sourceChain,destChain),
      forwardAck(sourceChain,destChain),
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
  run sendTransfer(sourceChain: str, destChain: str, tokens: List[Token], sender: Address, receiver: Address, forwadingPath: ForwardingPath): bool = (  
      sendPacket(sourceChain, destChain, tokens, sender, receiver,forwadingPath)
    ).then(
      receivePacket(sourceChain, destChain)
    ).then(
      receiveAck(sourceChain)
    )

  /****************************************************************************
   * TESTS For Forwarding - always use a single token
   ***************************************************************************/

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
run DetailedHappyPathTest = {
    pure val amount = 90

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
*/
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Tansfer happening from A to C using the forwarding path 
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
      sendTransfer("A", "B", [{denom:ATOM, amount: amount }], "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(all {
      // check that voucher exists on chain B
      val balanceB = getBalanceIn("B", "forward_account", denomSentFromAToB)
      assert(balanceB == amount),

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount),

      sendTransfer("B", "C", [{denom:denomSentFromAToB, amount: amount }], "forward_account", "charlie",[])
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


  /****************************************************************************
   * TESTS :Forwarding
   ***************************************************************************/


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 1 test 
  // Init function for scenario 1 
  action initScenario1 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0)) else if (chain == "B") Map("bob" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
    })
  }

// 
// Scenario 1 test 
    run Scenario1Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    
    pure val denomBC = denomInA.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomInA.path))
    
    pure val denomBCB = denomInA
    
    pure val denomCBA = denomBCB.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomBCB.path))
    
    initScenario1.then(
      // Make sure that Bob has enough tokens on chain B. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("B", "bob", ATOM, amount)
    ).then({
      // Normal Transfer B to C
      sendPacket("B", "C", [{denom:ATOM, amount: amount }], "bob", "charlie",[])
    }
    ).then(all{
      
       val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == amount), 
     
      receivePacket("B", "C") 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
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

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:denomBC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == amount), 
      
      // This time token get burned 
      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == 0),

      val balanceC = getBalanceIn("C", "escrow_account", denomBC)
      assert(balanceC == 0),
      
      receivePacket("C", "B") 
    }).then(all{
      
      val balanceBt2 = getBalanceIn("B", getForwardAccount("channelToC"), denomInA)
      assert(balanceBt2 == amount), 

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), denomInA)
      assert(balanceB2 == 0), 

      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == 0),   

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomInA)
      assert(balanceB3 == 0),   

      val balanceC = getBalanceIn("C", "escrow_account", denomBC)
      assert(balanceC == 0),  

      sendPacket("B", "A", [{denom:denomInA, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomInA)
      assert(balanceB2 == amount), 

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB3 == 0), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      failingReceivePacket("B", "A") 
        
    }).then(
      receiveAck("B") // Refund logic should be properly executed on B
    ).then(all{

      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), denomInA)
      assert(balanceB == 0), 
      
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == amount), // This should have been reverted to original state before start forwarding transfer. 

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomInA)
      assert(balanceB3 == 0), 

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 
      val balanceB = getBalanceIn("B", "bob", denomInA)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      assert(balanceB2 == amount), 

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomInA)
      assert(balanceB3 == 0), 

      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToC"), denomInA)
      assert(balanceB4 == 0), 

      val balanceB5 = getBalanceIn("B", getForwardAccount("channelToA"), denomInA)
      assert(balanceB5 == 0), 

      val balanceC = getBalanceIn("C", "charlie", denomBC)
      assert(balanceC == amount),
      
      val balanceC2 = getBalanceIn("C", "forward_account", denomBC)
      assert(balanceC2 == 0),
      
      val balanceC3 = getBalanceIn("C", "forward_account", denomBC)
      assert(balanceC3 == 0),
      
      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
 // Init function for scenario 2 
  action initScenario2 = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "C") Map("charlie" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
       // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: [] 
    })
  }

    run Scenario2Test = {
    pure val amount = 90

    pure val denomInA = ATOM
    pure val denomCB = denomInA.with("path", [{ port: "transfer", channel: "channelToC" }].concat(denomInA.path))
    pure val denomBA = denomCB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomCB.path))
    
    initScenario2.then(
      // Make sure that Charlie has enough tokens on chain C. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("C", "charlie", ATOM, amount)
    ).then(all{
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 

      val balanceB = getBalanceIn("B", "bob", denomCB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomCB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB3 == 0), 

      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == amount),
        
      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == 0),
      
      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0), 

      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:denomInA, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      
      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == 0),

      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == amount),

      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0),

      receivePacket("C", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomCB)
      assert(balanceB2 == 0),   

      val balanceC = getBalanceIn("C", "charlie", denomInA)
      assert(balanceC == 0),

      val balanceC2 = getBalanceIn("C", "escrow_account", denomInA)
      assert(balanceC2 == amount),

      val balanceC3 = getBalanceIn("C", "forward_account", denomInA)
      assert(balanceC3 == 0),
      

      sendPacket("B", "A", [{denom:denomCB, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomCB)
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

      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomCB)
      assert(balanceB2 == amount), 

      receiveAck("B") // Refund logic should be properly executed on B
    }).then(all{

      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomCB)
      assert(balanceB2 == 0), // This should have been reverted to original state before start forwarding transfer. 

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomCB)
      assert(balanceB3 == 0), // This should have been reverted to original state before start forwarding transfer. 
      

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 

      val balanceB = getBalanceIn("B", "bob", denomCB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), denomCB)
      assert(balanceB2 == 0),

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToC"), denomCB)
      assert(balanceB3 == 0), // This should have been reverted to original state before start forwarding transfer. 
      
      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToC"), denomCB)
      assert(balanceB4 == 0),

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomCB)
      assert(balanceB3 == 0), // This should have been reverted to original state before start forwarding transfer. 
      
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
      // All accounts are empty
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
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
      sendPacket("A", "B", [{denom:denomInA, amount: amount }], "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
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

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), denomAB)
      assert(balanceB2 == amount), 

      // Forwarding Transfer A -> B Completed 
     
      // Forwarding Transfer B to C
      sendPacket("B", "C", [{denom:denomAB, amount: amount }], getForwardAccount("channelToA"), "charlie",[])
    }
    ).then(all{
      
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), 

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), denomAB)
      assert(balanceB2 == 0), 
     
      receivePacket("B", "C") 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
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

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), 

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),

      // Precondition is met 

      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:denomABC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
 
      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == 0),

      // This time token get burned 
      val balanceC = getBalanceIn("C", "escrow_account", denomABC)
      assert(balanceC == 0),
      
      receivePacket("C", "B") 
    }).then(all{
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomAB)
      assert(balanceB == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == 0),   

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomAB)
      assert(balanceB3 == 0),  

      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToA"), denomAB)
      assert(balanceB4 == 0), 
      
      val balanceC = getBalanceIn("C", "escrow_account", denomABC)
      assert(balanceC == 0),  

      sendPacket("B", "A", [{denom:denomAB, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomAB)
      assert(balanceB == 0),

      // This time token get burned
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), denomAB)
      assert(balanceB2 == 0), 

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == 0), 

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomAB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      failingReceivePacket("B", "A") 
        
    }).then(
      receiveAck("B") // Refund logic should be properly executed on B
    ).then(all{
      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), denomAB)
      assert(balanceB == 0), // In the case nothing to revert
      
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), // This should have been reverted to original state before start forwarding transfer. 
      
      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 
      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), 

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),
      
      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 4 Test 
// In this scenario only Chain A and B are involved. No need to preset per channel escrow and forwarding addresses
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
      forwardedPacket: [],
      receivedTokens: []
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
      sendPacket("A", "B", [{denom:denomInA, amount: amount }], "alice", "alex",[{ port: "transfer", channel: "channelToA" }])
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
      

      sendPacket("B", "A", [{denom:denomAB, amount: amount }], "forward_account", "alex",[])
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
      receiveAck("B") // No Op in this case 
    }).then(all{

      val balanceB = getBalanceIn("B", "bob", denomAB)
      assert(balanceB == 0),
      
      val balanceB2 = getBalanceIn("B", "escrow_account", denomAB)
      assert(balanceB2 == 0),
      
      val balanceB3 = getBalanceIn("B", "forward_account", denomAB)
      assert(balanceB3 == 0), 

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

 // Initialize the protocol
  action initScenario5 = {
    chainStates' = CHAINS.mapBy(chain => {
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else Map(),
      channels: channelCounterparties.get(chain),
       channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
     // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
    })
  }

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
      sendPacket("A", "B", [{denom:ATOM, amount: amount }], "alice", "bob",[])
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
      sendPacket("B", "C", [{denom:denomAB, amount: amount }], "bob", "charlie",[])
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

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:denomABC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      receivePacket("C", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), denomAB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomAB)
      assert(balanceB2 == 0), 
      // Manipulate Escrow Balance on Chain A. This should be sufficient to make the transfer from B -> A succed
      // And the onRecv function on A to generate an error ack.       
      setBalanceIn("A", "escrow_account", ATOM, amount-1)  
    }).then(
      // The sendFungibleTokens here must succed  
      sendPacket("B", "A", [{denom:denomAB, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    ).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomAB)
      assert(balanceB == 0),
      //val balanceA = getBalanceIn("A", "alice", denomABC)
      //assert(balanceA == amount),
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), denomAB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      receivePacket("B", "A") // This fails because we have manipulated balance in A escrow_account 
        
    }).then(
      receiveAck("B") // Error ack is properly written here. // Refund logic properly executed on B
    ).then(all{
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), denomAB)
      assert(balanceB == 0),
      
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      val balanceC = getBalanceIn("C", "charlie", denomABC)
      assert(balanceC == amount),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomAB)
      assert(balanceB2 == amount),

      val balanceA = getBalanceIn("A", "escrow_account", denomInA)
      assert(balanceA == 89),

      // noop
      chainStates' = chainStates
      }
    )
  }


  /****************************************************************************
   * TESTS : Multidenom + Forwarding
   ***************************************************************************/

  action initX = {
    chainStates' = CHAINS.mapBy(chain => {
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0, OSMO ->0, ETH ->0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
    })
  }

run DetailedHappyPathTest = {
    pure val amount = 90

    pure val AtomDenomBase = ATOM
    pure val AtomDenomSentFromAToB = AtomDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(AtomDenomBase.path))
    pure val AtomDenomSentFromBToC = AtomDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(AtomDenomSentFromAToB.path))
    
    pure val OsmoDenomBase = OSMO
    pure val OsmoDenomSentFromAToB = OsmoDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(OsmoDenomBase.path))
    pure val OsmoDenomSentFromBToC = OsmoDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(OsmoDenomSentFromAToB.path))
    
    pure val EthDenomBase = ETH
    pure val EthDenomSentFromAToB = EthDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(EthDenomBase.path))
    pure val EthDenomSentFromBToC = EthDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(EthDenomSentFromAToB.path))
    

    initX.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", ATOM, amount)
    ).then(
      setBalanceIn("A", "alice", OSMO, amount)
    ).then(
      setBalanceIn("A", "alice", ETH, amount)
    ).then(
      sendPacket("A", "B", [{denom:ATOM, amount: amount },{denom:ETH, amount: amount }, {denom:OSMO, amount: amount } ], "alice", "charlie",[{ port: "transfer", channel: "channelToC" }])
    ).then(all{
      val balanceC = getBalanceIn("A", "alice", AtomDenomBase)
      assert(balanceC == 0),

      val balanceC = getBalanceIn("A", "alice", EthDenomBase)
      assert(balanceC == 0),

      val balanceC = getBalanceIn("A", "alice", OsmoDenomBase)
      assert(balanceC == 0),

      //  ).then(
      receivePacket("A", "B") 
    }).then(
      sendPacket("B", "C", [{denom:AtomDenomSentFromAToB, amount: amount },{denom:EthDenomSentFromAToB, amount: amount }, {denom:OsmoDenomSentFromAToB, amount: amount } ], "forward_account", "charlie",[])
    ).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B")
    ).then(
      receiveAck("A")
    ).then(all {
      // check that the balance is updated on chainC
      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromBToC)
      assert(balanceC == amount),

       val balanceC1 = getBalanceIn("C", "charlie", OsmoDenomSentFromBToC)
      assert(balanceC1 == amount),


       val balanceC2 = getBalanceIn("C", "charlie", EthDenomSentFromBToC)
      assert(balanceC2 == amount),

      // check that balance on chain B is empty
      val balanceB = getBalanceIn("B", "bob", AtomDenomSentFromAToB)
      assert(balanceB == 0),
      // check the escrow_account balance on chain B is amount
      val balanceB2 = getBalanceIn("B", "escrow_account", AtomDenomSentFromAToB)
      assert(balanceB2 == amount),

      val balanceB2 = getBalanceIn("B", "escrow_account", OsmoDenomSentFromAToB)
      assert(balanceB2 == amount),

      val balanceB2 = getBalanceIn("B", "escrow_account", EthDenomSentFromAToB)
      assert(balanceB2 == amount),

      // check that balance on chain A is empty
      val balanceA = getBalanceIn("A", "alice", AtomDenomBase)
      assert(balanceA == 0),
      // check the escrow_account balance on chain A is amount
      val balanceA = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA == amount),

         val balanceA = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA == amount),

         val balanceA = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA == amount),

      // noop
      chainStates' = chainStates
      }
    )
  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scenario 1  multidenom + forwarding test 
  // Init function for scenario 1 
  action initScenario1mf = {
    chainStates' = CHAINS.mapBy(chain => {
      // All accounts are empty, except for Alice in chain A who has 100 atoms
      //bank: if (chain == "A") Map("alice" -> Map(ATOM -> 100)) else if (chain == "B") Map("bob" -> Map(ATOM -> 100)) else if (chain == "C") Map("charlie" -> Map(ATOM -> 100)) else Map(),
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0)) else if (chain == "B") Map("bob" -> Map(ATOM -> 0, OSMO ->0, ETH ->0)) else Map(),
      channels: channelCounterparties.get(chain),
      channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
      // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
    })
  }

// 
// Scenario 1 test 
    run Scenario1mfTest = {
    pure val amount = 90
    pure val AtomDenomBase = ATOM
    pure val AtomDenomSentFromBToC = AtomDenomBase.with("path", [{ port: "transfer", channel: "channelToB" }].concat(AtomDenomBase.path))
    pure val AtomDenomSentFromCToBtoA = AtomDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(AtomDenomBase.path))
    
    pure val OsmoDenomBase = OSMO
    pure val OsmoDenomSentFromBToC = OsmoDenomBase.with("path", [{ port: "transfer", channel: "channelToB" }].concat(OsmoDenomBase.path))
    pure val OsmoDenomSentFromCToBtoA = OsmoDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(OsmoDenomBase.path))
    
    pure val EthDenomBase = ETH
    pure val EthDenomSentFromBToC = EthDenomBase.with("path", [{ port: "transfer", channel: "channelToB" }].concat(EthDenomBase.path))
    pure val EthDenomSentFromCToBtoA = EthDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(EthDenomBase.path))
    
    initScenario1mf.then(
      // Make sure that Bob has enough tokens on chain B. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("B", "bob", AtomDenomBase, amount)
    ).then(
      setBalanceIn("B", "bob", OsmoDenomBase, amount)
    ).then(
      setBalanceIn("B", "bob", EthDenomBase, amount)
    ).then({
      // Normal Transfer B to C
      sendPacket("B", "C", [{denom:AtomDenomBase, amount: amount }, {denom:OsmoDenomBase, amount: amount }, {denom:EthDenomBase, amount: amount }], "bob", "charlie",[])
    }
    ).then(all{
      
       val balanceB = getBalanceIn("B", "bob", AtomDenomBase)
      assert(balanceB == 0),

      val balanceB = getBalanceIn("B", "bob", EthDenomBase)
      assert(balanceB == 0),

      val balanceB = getBalanceIn("B", "bob", OsmoDenomBase)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomBase)
      assert(balanceB2 == amount), 

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomBase)
      assert(balanceB2 == amount), 

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomBase)
      assert(balanceB2 == amount), 
     
      receivePacket("B", "C") 
    }).then(all{

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromBToC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromBToC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", EthDenomSentFromBToC)
      assert(balanceC == amount),

      receiveAck("B") 
    }).then(all{
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 
      // No Op. Nothing Happened
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:AtomDenomSentFromBToC, amount: amount }, {denom:OsmoDenomSentFromBToC, amount: amount }, {denom:EthDenomSentFromBToC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{

      // This time token get burned 
      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromBToC)
      assert(balanceC == 0),
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromBToC)
      assert(balanceC == 0),
      val balanceC = getBalanceIn("C", "charlie", EthDenomSentFromBToC)
      assert(balanceC == 0),
      // Nothing is credited to escrow_account 
      val balanceC = getBalanceIn("C", "escrow_account", AtomDenomSentFromBToC)
      assert(balanceC == 0),
      val balanceC = getBalanceIn("C", "escrow_account", OsmoDenomSentFromBToC)
      assert(balanceC == 0),
      val balanceC = getBalanceIn("C", "escrow_account", EthDenomSentFromBToC)
      assert(balanceC == 0),
      
      receivePacket("C", "B") 
    }).then(all{
      
      val balanceBt2 = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomBase)
      assert(balanceBt2 == amount), 
      val balanceBt2 = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomBase)
      assert(balanceBt2 == amount), 
      val balanceBt2 = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomBase)
      assert(balanceBt2 == amount), 

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), AtomDenomBase)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), OsmoDenomBase)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToA"), EthDenomBase)
      assert(balanceB2 == 0), 

      // escrow_account on B should be 0
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomBase)
      assert(balanceB2 == 0),   
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomBase)
      assert(balanceB2 == 0),   
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomBase)
      assert(balanceB2 == 0),   

      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomBase)
      assert(balanceB3 == 0),   
      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomBase)
      assert(balanceB3 == 0),   
      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomBase)
      assert(balanceB3 == 0),   
      
      //val balanceC = getBalanceIn("C", "escrow_account", denomBC)
      //assert(balanceC == 0),  

      sendPacket("B", "A", [{denom:AtomDenomBase, amount: amount }, {denom:OsmoDenomBase, amount: amount }, {denom:EthDenomBase, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    }).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), AtomDenomBase)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), OsmoDenomBase)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), EthDenomBase)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomBase)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomBase)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomBase)
      assert(balanceB2 == amount), 

      // Here during onRecv packet an error ack must be written.  
      // Probably here we should create a fakeErrorReceive. Here token are minted for the first time. How to make it error?
      // I can't imagine a scenario to make this fail without doing a previous transfer A to B 
      // I'll mock the erorr. 
      // Change the balance into B escrow account to make the receive function fail 
      //setBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomBase, amount-1)
      failingReceivePacket("B", "A") 
    //}).then({

    // receivePacket("B", "A") 
        
    }).then(
      receiveAck("B") // Refund logic should be properly executed on B
    ).then(all{

      //val balanceB = getBalanceIn("B", getForwardAccount("channelToA"), AtomDenomBase)
      //assert(balanceB == 0), 
      
      //val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), denomInA)
      //assert(balanceB2 == amount), // This should have been reverted to original state before start forwarding transfer. 

      //val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), denomInA)
      //assert(balanceB3 == 0), 

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      // Check the final chains states are equal to the ones before starting the forwardingTransfer 
      val balanceB = getBalanceIn("B", "bob", AtomDenomBase)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomBase)
      assert(balanceB2 == amount), 
      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomBase)
      assert(balanceB3 == 0), 
      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomBase)
      assert(balanceB4 == 0), 
      val balanceB5 = getBalanceIn("B", getForwardAccount("channelToA"), AtomDenomBase)
      assert(balanceB5 == 0), 

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomBase)
      assert(balanceB2 == amount), 
      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomBase)
      assert(balanceB3 == 0), 
      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomBase)
      assert(balanceB4 == 0), 
      val balanceB5 = getBalanceIn("B", getForwardAccount("channelToA"), OsmoDenomBase)
      assert(balanceB5 == 0), 


      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomBase)
      assert(balanceB2 == amount), 
      val balanceB3 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomBase)
      assert(balanceB3 == 0), 
      val balanceB4 = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomBase)
      assert(balanceB4 == 0), 
      val balanceB5 = getBalanceIn("B", getForwardAccount("channelToA"), EthDenomBase)
      assert(balanceB5 == 0), 

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromBToC)
      assert(balanceC == amount),
      val balanceC2 = getBalanceIn("C", "forward_account", AtomDenomSentFromBToC)
      assert(balanceC2 == 0),
      val balanceC3 = getBalanceIn("C", "forward_account", AtomDenomSentFromBToC)
      assert(balanceC3 == 0),
      
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromBToC)
      assert(balanceC == amount),
      val balanceC2 = getBalanceIn("C", "forward_account", OsmoDenomSentFromBToC)
      assert(balanceC2 == 0),
      val balanceC3 = getBalanceIn("C", "forward_account", OsmoDenomSentFromBToC)
      assert(balanceC3 == 0),
      

      val balanceC = getBalanceIn("C", "charlie", EthDenomSentFromBToC)
      assert(balanceC == amount),
      val balanceC2 = getBalanceIn("C", "forward_account", EthDenomSentFromBToC)
      assert(balanceC2 == 0),
      val balanceC3 = getBalanceIn("C", "forward_account", EthDenomSentFromBToC)
      assert(balanceC3 == 0),
      // noop
      chainStates' = chainStates
      }
    )
  }


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Now to test proper errors with multidenom we will use scenario 5 test and we will manipulate the balance 
// of a certain token 

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


// Scenario5 Test First Token Failing
// We want to test C->B->A with an error ack happening on B->A. Thus we want to verify everything get reverted properly 
 // Initialize the protocol
  action initScenario5mf = {
    chainStates' = CHAINS.mapBy(chain => {
      bank: if (chain == "A") Map("alice" -> Map(ATOM -> 0, OSMO ->0, ETH ->0)) else Map(),
      channels: channelCounterparties.get(chain),
       channelEscrowAddresses: if (chain == "B") Map("channelToA" -> "escrow_account_a","channelToC" -> "escrow_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => ESCROW_ACCOUNT),
      // Verify what channelForwardingAddresses should be initialized to 
      channelForwardingAddresses: if (chain == "B") Map("channelToA" -> "forward_account_a","channelToC" -> "forward_account_c" ) else channelCounterparties.get(chain).keys().mapBy(_ => "forward_account"), 
     // Start without any unprocessed packets/acknowledgements/timeouts
      outPackets: Set(),
      receivedButUnacknowledgedPackets: Set(),
      inAcknowledgements: Set(),
      inTimeouts: Set(),
      forwardedPacket: [],
      receivedTokens: []
    })
  }

  run Scenario5mfFirstTokenTest = {
    pure val amount = 90

    pure val AtomDenomBase = ATOM
    pure val AtomDenomSentFromAToB = AtomDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(AtomDenomBase.path))
    pure val AtomDenomSentFromAToBtoC = AtomDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(AtomDenomSentFromAToB.path))
    
    pure val OsmoDenomBase = OSMO
    pure val OsmoDenomSentFromAToB = OsmoDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(OsmoDenomBase.path))
    pure val OsmoDenomSentFromAToBtoC = OsmoDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(OsmoDenomSentFromAToB.path))
    
    pure val EthDenomBase = ETH
    pure val EthDenomSentFromAToB = EthDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(EthDenomBase.path))
    pure val EthDenomSentFromAToBtoC = EthDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(EthDenomSentFromAToB.path))
    
    pure val denomInA = ATOM
    pure val denomAB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomABC = denomAB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomAB.path))
    
    initScenario5mf.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", AtomDenomBase, amount)
    ).then(
      setBalanceIn("A", "alice", OsmoDenomBase, amount)
    ).then(
      setBalanceIn("A", "alice", EthDenomBase, amount)
    ).then(
      // Normal Transfer A to B
      sendPacket("A", "B", [{denom:AtomDenomBase, amount: amount }, {denom:OsmoDenomBase, amount: amount }, {denom:EthDenomBase, amount: amount }], "alice", "bob",[])
    ).then(
      receivePacket("A", "B") 
    ).then(
      receiveAck("A") 
    ).then(all{
      
      // alice balance should be 0 
      val balanceA = getBalanceIn("A", "alice", AtomDenomBase)
      assert(balanceA == 0),  
      val balanceA = getBalanceIn("A", "alice", OsmoDenomBase)
      assert(balanceA == 0),  
      val balanceA = getBalanceIn("A", "alice", OsmoDenomBase)
      assert(balanceA == 0), 
      // escrow_account on A should be amount  
      val balanceA2 = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA2 == amount), 
      val balanceA2 = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA2 == amount), 
      val balanceA2 = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA2 == amount), 
      
      // bob balance on B should B amount
      val balanceB = getBalanceIn("B", "bob", AtomDenomSentFromAToB)
      assert(balanceB == amount), 
      val balanceB = getBalanceIn("B", "bob", OsmoDenomSentFromAToB)
      assert(balanceB == amount), 
      val balanceB = getBalanceIn("B", "bob", EthDenomSentFromAToB)
      assert(balanceB == amount), 

      // Normal Transfer B to C
      sendPacket("B", "C", [{denom:AtomDenomSentFromAToB, amount: amount },{denom:OsmoDenomSentFromAToB, amount: amount },{denom:EthDenomSentFromAToB, amount: amount }], "bob", "charlie",[])
    }).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B") 
    ).then(all{
      //assert(false),
      // Again same checks on B and C 
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 
      val balanceA = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA == amount),

      val balanceB = getBalanceIn("B", "bob", AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", "bob", OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", "bob", EthDenomSentFromAToB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", EthDenomSentFromAToBtoC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:AtomDenomSentFromAToBtoC, amount: amount },{denom:OsmoDenomSentFromAToBtoC, amount: amount },{denom:EthDenomSentFromAToBtoC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      receivePacket("C", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomSentFromAToB)
      assert(balanceB2 == 0), 
      
      // Manipulate Escrow Balance on Chain A. This should be sufficient to make the transfer from B -> A succed
      // And the onRecv function on A to generate an error ack.       
      setBalanceIn("A", "escrow_account", AtomDenomBase, amount-1)  
    }).then(
      // The sendFungibleTokens here must succed  
      sendPacket("B", "A", [{denom:AtomDenomSentFromAToB, amount: amount },{denom:OsmoDenomSentFromAToB, amount: amount },{denom:EthDenomSentFromAToB, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    ).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == 0),
      

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomSentFromAToB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      receivePacket("B", "A") // This fails because we have manipulated balance in A escrow_account 
        
    }).then(
      receiveAck("B") // Error ack is properly written here. // Refund logic properly executed on B
    ).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == 0),
      
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromAToBtoC)
      assert(balanceC == amount),
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount),
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount),
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount),

      val balanceA = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA == 89), // Same as the modified balance
      val balanceA = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA == amount),

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


// Scenario5 Test Last Token Failing
// We want to test C->B->A with an error ack happening on B->A. Thus we want to verify everything get reverted properly 
 // Initialize the protocol
  run Scenario5mfLastTokenTest = {
    pure val amount = 90

    pure val AtomDenomBase = ATOM
    pure val AtomDenomSentFromAToB = AtomDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(AtomDenomBase.path))
    pure val AtomDenomSentFromAToBtoC = AtomDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(AtomDenomSentFromAToB.path))
    
    pure val OsmoDenomBase = OSMO
    pure val OsmoDenomSentFromAToB = OsmoDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(OsmoDenomBase.path))
    pure val OsmoDenomSentFromAToBtoC = OsmoDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(OsmoDenomSentFromAToB.path))
    
    pure val EthDenomBase = ETH
    pure val EthDenomSentFromAToB = EthDenomBase.with("path", [{ port: "transfer", channel: "channelToA" }].concat(EthDenomBase.path))
    pure val EthDenomSentFromAToBtoC = EthDenomSentFromAToB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(EthDenomSentFromAToB.path))
    
    pure val denomInA = ATOM
    pure val denomAB = denomInA.with("path", [{ port: "transfer", channel: "channelToA" }].concat(denomInA.path))
    pure val denomABC = denomAB.with("path", [{ port: "transfer", channel: "channelToB" }].concat(denomAB.path))
    
    initScenario5mf.then(
      // Make sure that Alice has enough tokens on chain A. In the go test, this
      // is implicitly done somewhere in the test environment setup.
      setBalanceIn("A", "alice", AtomDenomBase, amount)
    ).then(
      setBalanceIn("A", "alice", OsmoDenomBase, amount)
    ).then(
      setBalanceIn("A", "alice", EthDenomBase, amount)
    ).then(
      // Normal Transfer A to B
      sendPacket("A", "B", [{denom:AtomDenomBase, amount: amount }, {denom:OsmoDenomBase, amount: amount }, {denom:EthDenomBase, amount: amount }], "alice", "bob",[])
    ).then(
      receivePacket("A", "B") 
    ).then(
      receiveAck("A") 
    ).then(all{
      
      // alice balance should be 0 
      val balanceA = getBalanceIn("A", "alice", AtomDenomBase)
      assert(balanceA == 0),  
      val balanceA = getBalanceIn("A", "alice", OsmoDenomBase)
      assert(balanceA == 0),  
      val balanceA = getBalanceIn("A", "alice", OsmoDenomBase)
      assert(balanceA == 0), 
      // escrow_account on A should be amount  
      val balanceA2 = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA2 == amount), 
      val balanceA2 = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA2 == amount), 
      val balanceA2 = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA2 == amount), 
      
      // bob balance on B should B amount
      val balanceB = getBalanceIn("B", "bob", AtomDenomSentFromAToB)
      assert(balanceB == amount), 
      val balanceB = getBalanceIn("B", "bob", OsmoDenomSentFromAToB)
      assert(balanceB == amount), 
      val balanceB = getBalanceIn("B", "bob", EthDenomSentFromAToB)
      assert(balanceB == amount), 

      // Normal Transfer B to C
      sendPacket("B", "C", [{denom:AtomDenomSentFromAToB, amount: amount },{denom:OsmoDenomSentFromAToB, amount: amount },{denom:EthDenomSentFromAToB, amount: amount }], "bob", "charlie",[])
    }).then(
      receivePacket("B", "C") 
    ).then(
      receiveAck("B") 
    ).then(all{
      //assert(false),
      // Again same checks on B and C 
      // The chain state before starting the forwardingTransfer should be like this. 
      // Thus at the end of the test we should have the exact chain state that we see here. 
      val balanceA = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA == amount),

      val balanceB = getBalanceIn("B", "bob", AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", "bob", OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", "bob", EthDenomSentFromAToB)
      assert(balanceB == 0),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount), 

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceC = getBalanceIn("C", "charlie", EthDenomSentFromAToBtoC)
      assert(balanceC == amount),
      // Start Forwarding Transfer C -> B -> A
      sendPacket("C", "B", [{denom:AtomDenomSentFromAToBtoC, amount: amount },{denom:OsmoDenomSentFromAToBtoC, amount: amount },{denom:EthDenomSentFromAToBtoC, amount: amount }], "charlie", "alice",[{ port: "transfer", channel: "channelToA" }])
    }).then(all{
      receivePacket("C", "B") 
    }).then(all{

      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount), 
      val balanceB2 = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount), 
      // escrow_account on B should be 0

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomSentFromAToB)
      assert(balanceB2 == 0), 
      
      // Manipulate Escrow Balance on Chain A. This should be sufficient to make the transfer from B -> A succed
      // And the onRecv function on A to generate an error ack.       
      setBalanceIn("A", "escrow_account", EthDenomBase, amount-1)  
    }).then(
      // The sendFungibleTokens here must succed  
      sendPacket("B", "A", [{denom:AtomDenomSentFromAToB, amount: amount },{denom:OsmoDenomSentFromAToB, amount: amount },{denom:EthDenomSentFromAToB, amount: amount }], getForwardAccount("channelToC"), "alice",[])
    ).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == 0),
      

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), AtomDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), OsmoDenomSentFromAToB)
      assert(balanceB2 == 0), 
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToA"), EthDenomSentFromAToB)
      assert(balanceB2 == 0), 

      // Here during onRecv packet an error ack must be written.  
      receivePacket("B", "A") // This fails because we have manipulated balance in A escrow_account 
        
    }).then(
      receiveAck("B") // Error ack is properly written here. // Refund logic properly executed on B
    ).then(all{
      
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == 0),
      val balanceB = getBalanceIn("B", getForwardAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == 0),
      
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      val balanceB = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB == amount), // This should have been reverted to original state before start forwarding transfer. 
      

      forwardAck("B","C") // AdHoc ForwardAck function. Needed to pick the right acknw
      }
       
    ).then(all {

      val balanceC = getBalanceIn("C", "charlie", AtomDenomSentFromAToBtoC)
      assert(balanceC == amount),
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),
      val balanceC = getBalanceIn("C", "charlie", OsmoDenomSentFromAToBtoC)
      assert(balanceC == amount),

      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), AtomDenomSentFromAToB)
      assert(balanceB2 == amount),
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), OsmoDenomSentFromAToB)
      assert(balanceB2 == amount),
      val balanceB2 = getBalanceIn("B", getEscrowAccount("channelToC"), EthDenomSentFromAToB)
      assert(balanceB2 == amount),

      val balanceA = getBalanceIn("A", "escrow_account", AtomDenomBase)
      assert(balanceA == amount), // Same as the modified balance
      val balanceA = getBalanceIn("A", "escrow_account", OsmoDenomBase)
      assert(balanceA == amount),
      val balanceA = getBalanceIn("A", "escrow_account", EthDenomBase)
      assert(balanceA == 89),

      // noop
      chainStates' = chainStates
      }
    )
  }


/* ***************************************************************************
   * INVARIANTS
   * **************************************************************************/

  // To check in random simulator:
  // $ quint run --main=ics20Test --invariant=BalanceNonNegative ics20.qnt
 // quint run --max-samples=1000 --max-steps=1000 --invariant=BalanceNonNegative --main=ics20v2Test ics20v2.qnt --verbosity=2
  // The balance of all denominations in all accounts is always non-negative.
  val BalanceNonNegative = CHAINS.forall(chain =>
      USER_ACCOUNTS.forall(addr =>
        chainStates.get(chain).bank.getBalances(addr).getBalance(ATOM) >= 0
    )
  )

  // Add invariants 
  // 1. SUM USERS BALANCE IS CONSTANT = Amount 
  // 2. Denoms amount are constant = amount

}
