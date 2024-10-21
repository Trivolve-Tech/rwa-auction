use aiken/hash.{Blake2b_224, Hash}
use aiken/interval
use aiken/list
use aiken/option
use aiken/time.{PosixTime}
use aiken/transaction.{
  InlineDatum, Input, NoDatum, Output, OutputReference, ScriptContext, Spend,
  Transaction, TransactionId, ValidityRange, find_input,
}
use aiken/transaction/credential.{
  Address, VerificationKey, VerificationKeyCredential,
}
use aiken/transaction/value.{
  AssetName, PolicyId, Value, ada_asset_name, ada_policy_id,
}

type PubKeyHash =
  Hash<Blake2b_224, VerificationKey>

// ---------------------------------------------------------------------

type Bid {
  bidOwner: PubKeyHash,
  value: Int,
}

type LotDatum {
  seller: PubKeyHash,
  deadline: PosixTime,
  minBid: Int,
  policy_id: PolicyId,
  asset_name: AssetName,
  highestBid: Option<Bid>,
}

type AuctionRedeemer {
  MakeBid(Bid)
  Close
}

validator {
  fn auction(
    data: LotDatum,
    redeemer: AuctionRedeemer,
    ctx: ScriptContext,
  ) -> Bool {
    expect Spend(ownOutputRef) = ctx.purpose
    expect Some(ownInput) = find_input(ctx.transaction.inputs, ownOutputRef)

    let getOwnOutput =
      fn() -> Output {
        expect [ownOutput] = {
          let isOwnOutput =
            fn(o: Output) -> Bool { o.address == ownInput.output.address }
          ctx.transaction.outputs |> list.filter(isOwnOutput)
        }
        ownOutput
      }

    let sufficientBid =
      fn(bid: Bid) -> Bool {
        when data.highestBid is {
          None -> data.minBid <= bid.value
          Some(oldBid) -> oldBid.value < bid.value
        }
      }

    let correctBidOutputDatum =
      fn(bid: Bid) -> Bool {
        expect InlineDatum(ownOutputDatumUntyped) = getOwnOutput().datum
        expect ownOutputDatum: LotDatum = ownOutputDatumUntyped

        data.seller == ownOutputDatum.seller && data.deadline == ownOutputDatum.deadline && data.minBid == ownOutputDatum.minBid && data.policy_id == ownOutputDatum.policy_id && data.asset_name == ownOutputDatum.asset_name && Some(
          bid,
        ) == ownOutputDatum.highestBid
      }

    let correctBidOutputValue =
      fn(bid: Int) -> Bool {
        getOwnOutput().value == (
          value.from_lovelace(bid)
            |> value.add(data.policy_id, data.asset_name, 1)
        )
      }

    let getValueSentToAddress =
      fn(address: PubKeyHash, policy_id: PolicyId, asset_name: AssetName) -> Int {
        let f =
          fn(o: Output, i: Int) -> Int {
            if
            o.address.payment_credential == VerificationKeyCredential(address){
            
              i + value.quantity_of(o.value, policy_id, asset_name)
            } else {
              i
            }
          }
        list.foldr(ctx.transaction.outputs, 0, f)
      }

    let correctBidRefund =
      fn() -> Bool {
        when data.highestBid is {
          None -> True
          Some(bid) ->
            getValueSentToAddress(bid.bidOwner, ada_policy_id, ada_asset_name) >= bid.value
        }
      }

    let correctBidSlotRange =
      fn() -> Bool {
        interval.is_entirely_before(
          ctx.transaction.validity_range,
          data.deadline,
        )
      }

    let correctCloseSlotRange =
      fn() -> Bool {
        interval.is_entirely_after(
          ctx.transaction.validity_range,
          data.deadline,
        )
      }

    let sellerGetsToken =
      fn() -> Bool {
        getValueSentToAddress(data.seller, data.policy_id, data.asset_name) >= 1
      }

    let highestBidderGetsToken =
      fn(bid: Bid) -> Bool {
        getValueSentToAddress(bid.bidOwner, data.policy_id, data.asset_name) >= 1
      }

    let sellerGetsHighestBid =
      fn(bid: Bid) -> Bool {
        getValueSentToAddress(data.seller, ada_policy_id, ada_asset_name) >= bid.value
      }

    let correctClose =
      fn() -> Bool {
        when data.highestBid is {
          None -> sellerGetsToken()?

          Some(bid) ->
            highestBidderGetsToken(bid)? && sellerGetsHighestBid(bid)?
        }
      }

    when redeemer is {
      MakeBid(bid) ->
        sufficientBid(bid)? && correctBidOutputDatum(bid)? && correctBidOutputValue(
          bid.value,
        )? && correctBidRefund()? && correctBidSlotRange()?

      Close -> correctClose() && correctCloseSlotRange()?
    }
  }
}
