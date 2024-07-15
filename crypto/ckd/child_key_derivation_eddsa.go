// Copyright © Swingby

package ckd

import (
	"bytes"
	"crypto/elliptic"
	"crypto/hmac"
	"crypto/sha512"
	"encoding/binary"
	"errors"
	"math/big"

	"github.com/bnb-chain/tss-lib/v2/common"
	"github.com/bnb-chain/tss-lib/v2/crypto"
	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcutil/base58"
	"github.com/decred/dcrd/dcrec/edwards/v2"
)

type ExtendedKeyEddsa struct {
	PublicKey  *crypto.ECPoint
	Depth      uint8
	ChildIndex uint32
	ChainCode  []byte // 32 bytes
	ParentFP   []byte // parent fingerprint
	Version    []byte
}

// For more information about child key derivation see https://github.com/binance-chain/tss-lib/issues/104
// https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki .
// The functions below do not implement the full BIP-32 specification. As mentioned in the Jira ticket above,
// we only use non-hardened derived keys.

const (

	// HardenedKeyStart hardened key starts.
	EDDSA_HardenedKeyStart = 0x80000000 // 2^31

	// max Depth
	eddsa_maxDepth = 1<<8 - 1

	Eddsa_PubKeyBytesLenCompressed = 33
)

// Extended public key serialization, defined in BIP32
func (k *ExtendedKeyEddsa) String() string {
	// version(4) || depth(1) || parentFP (4) || childinde(4) || chaincode (32) || key(33) || checksum(4)
	var childNumBytes [4]byte
	binary.BigEndian.PutUint32(childNumBytes[:], k.ChildIndex)

	serializedBytes := make([]byte, 0, serializedKeyLen+4)
	serializedBytes = append(serializedBytes, k.Version...)
	serializedBytes = append(serializedBytes, k.Depth)
	serializedBytes = append(serializedBytes, k.ParentFP...)
	serializedBytes = append(serializedBytes, childNumBytes[:]...)
	serializedBytes = append(serializedBytes, k.ChainCode...)
	edwards_pub := edwards.NewPublicKey(k.PublicKey.X(), k.PublicKey.Y())
	pubKeyBytes := CompressEDDSAPubKey(edwards_pub)
	serializedBytes = append(serializedBytes, pubKeyBytes...)

	checkSum := doubleHashB(serializedBytes)[:4]
	serializedBytes = append(serializedBytes, checkSum...)
	return base58.Encode(serializedBytes)
}

// NewExtendedKeyFromString returns a new extended key from a base58-encoded extended key
func NewExtendedKeyEddsaFromString(key string, curve elliptic.Curve) (*ExtendedKeyEddsa, error) {
	// version(4) || depth(1) || parentFP (4) || childinde(4) || chaincode (32) || key(33) || checksum(4)

	decoded := base58.Decode(key)
	if len(decoded) != serializedKeyLen+4 {
		return nil, errors.New("invalid extended key")
	}

	// Split the payload and checksum up and ensure the checksum matches.
	payload := decoded[:len(decoded)-4]
	checkSum := decoded[len(decoded)-4:]
	expectedCheckSum := doubleHashB(payload)[:4]
	if !bytes.Equal(checkSum, expectedCheckSum) {
		return nil, errors.New("invalid extended key")
	}

	// Deserialize each of the payload fields.
	version := payload[:4]
	depth := payload[4:5][0]
	parentFP := payload[5:9]
	childNum := binary.BigEndian.Uint32(payload[9:13])
	chainCode := payload[13:45]
	keyData := payload[45:78]

	var pubKey *crypto.ECPoint
	var err error

	if c, ok := curve.(*btcec.KoblitzCurve); ok {
		pk, err := btcec.ParsePubKey(keyData)
		if err != nil {
			return nil, err
		}
		pubKey, err = crypto.NewECPoint(c, pk.X(), pk.Y())
		if err != nil {
			return nil, err
		}
	} else {
		px, py := elliptic.Unmarshal(curve, keyData)
		pubKey, err = crypto.NewECPoint(curve, px, py)
		if err != nil {
			return nil, err
		}
	}

	return &ExtendedKeyEddsa{
		PublicKey:  pubKey,
		Depth:      depth,
		ChildIndex: childNum,
		ChainCode:  chainCode,
		ParentFP:   parentFP,
		Version:    version,
	}, nil
}

func DeriveChildKeyFromHierarchyEddsa(indicesHierarchy []uint32, pk *ExtendedKeyEddsa, mod *big.Int, curve elliptic.Curve) (*big.Int, *ExtendedKeyEddsa, error) {
	var k = pk
	var err error
	var childKey *ExtendedKeyEddsa
	mod_ := common.ModInt(mod)
	ilNum := big.NewInt(0)
	for index := range indicesHierarchy {
		ilNumOld := ilNum
		ilNum, childKey, err = DeriveChildKeyEddssa(indicesHierarchy[index], k, curve)
		if err != nil {
			return nil, nil, err
		}
		k = childKey
		ilNum = mod_.Add(ilNum, ilNumOld)
	}
	return ilNum, k, nil
}

// DeriveChildKey Derive a child key from the given parent key. The function returns "IL" ("I left"), per BIP-32 spec. It also
// returns the derived child key.
func DeriveChildKeyEddssa(index uint32, pk *ExtendedKeyEddsa, curve elliptic.Curve) (*big.Int, *ExtendedKeyEddsa, error) {
	if index >= EDDSA_HardenedKeyStart {
		return nil, nil, errors.New("the index must be non-hardened")
	}
	if pk.Depth == eddsa_maxDepth {
		return nil, nil, errors.New("cannot derive key beyond max depth")
	}

	cryptoPk := pk.PublicKey

	pub := edwards.NewPublicKey(pk.PublicKey.X(), pk.PublicKey.Y())
	data := make([]byte, 37)
	pkPublicKeyBytes := CompressEDDSAPubKey(pub)
	copy(data[:], pkPublicKeyBytes[:])

	binary.BigEndian.PutUint32(data[33:], index)

	// I = HMAC-SHA512(Key = chainCode, Data=data)
	hmac512 := hmac.New(sha512.New, pk.ChainCode)
	hmac512.Write(data)
	ilr := hmac512.Sum(nil)
	il := ilr[:32]
	childChainCode := ilr[32:]
	ilNum := new(big.Int).SetBytes(il)
	ilNum = ilNum.Mod(ilNum, curve.Params().N)

	var err error
	if ilNum.Cmp(curve.Params().N) >= 0 || ilNum.Sign() == 0 {
		// falling outside of the valid range for curve private keys
		err = errors.New("invalid derived key")
		common.Logger.Error("error deriving child key")
		return nil, nil, err
	}

	deltaG := crypto.ScalarBaseMult(curve, ilNum)
	if deltaG.X().Sign() == 0 || deltaG.Y().Sign() == 0 {
		err = errors.New("invalid child")
		common.Logger.Error("error invalid child")
		return nil, nil, err
	}
	childCryptoPk, err := cryptoPk.Add(deltaG)
	if err != nil {
		common.Logger.Error("error adding delta G to parent key")
		return nil, nil, err
	}

	childPk := &ExtendedKeyEddsa{
		PublicKey:  childCryptoPk,
		Depth:      pk.Depth + 1,
		ChildIndex: index,
		ChainCode:  childChainCode,
		ParentFP:   hash160(pkPublicKeyBytes)[:4],
		Version:    pk.Version,
	}
	return ilNum, childPk, nil
}

// CompressEDDSAPubKey serializes a public key 33-byte compressed format.
func CompressEDDSAPubKey(pubKey *edwards.PublicKey) []byte {
	b := make([]byte, 0, 33)
	b = append(b, 0x0)
	b = append(b, pubKey.SerializeCompressed()...)

	return b
}
