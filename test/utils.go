// Copyright © 2019 Binance
//
// This file is part of Binance. The full Binance copyright notice, including
// terms governing use, modification, and redistribution, is contained in the
// file LICENSE at the root of the source code distribution tree.

package test

import (
	"github.com/bnb-chain/tss-lib/v2/common"
	"github.com/bnb-chain/tss-lib/v2/tss"
)

func SharedPartyUpdater(party tss.Party, msg tss.Message, errCh chan<- *tss.Error) {
	common.Logger.Info("the party is ", party, " the msg is ", msg)
	// do not send a message from this party back to itself
	if party.PartyID() == msg.GetFrom() {
		common.Logger.Info("the party id is ", party.PartyID(), " return ")
		return
	}
	bz, _, err := msg.WireBytes()
	if err != nil {
		errCh <- party.WrapError(err)
		return
	}
	pMsg, err := tss.ParseWireMessage(bz, msg.GetFrom(), msg.IsBroadcast())
	if err != nil {
		errCh <- party.WrapError(err)
		return
	}
	if _, err := party.Update(pMsg); err != nil {
		errCh <- err
	}
}
