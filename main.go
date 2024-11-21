package main

import (
	"fmt"
	"os"
	"reilabs/whir-verifier-circuit/keccakSponge"
	"reilabs/whir-verifier-circuit/typeConverters"

	"github.com/consensys/gnark/frontend"
	go_ark_serialize "github.com/reilabs/go-ark-serialize"
)

type Circuit struct {
	IOPattern            []frontend.Variable     `gnark:"Input output pattern for the protocol. Used to seed the initial sponge"`
	MerkleRoot           []frontend.Variable     `gnark:"Merkle root for the Reed-Solomon encoding of the polynomial"`
	First_OOD_Answer     []frontend.Variable     `gnark:"First out-of-domain query answer"`
	Evaluation           frontend.Variable       `gnark:"Supposed evaluation for the Verifier query"`
	SumcheckPolysAsEvals [][][]frontend.Variable `gnark:"Quadratic sumcheck polynomials in their evaluation form (Evaluated over 0, 1, 2)"`
	FoldingParameter     int
}

func initializeSpongeWithIOPatternAndMerkleRoot(circuit *Circuit, api frontend.API) *keccakSponge.Digest {
	helperSponge, _ := keccakSponge.NewKeccak(api)
	helperSponge.Absorb(circuit.IOPattern)
	mainSponge, _ := keccakSponge.NewKeccakWithTag(api, helperSponge.Squeeze(32))
	mainSponge.Absorb(circuit.MerkleRoot)
	_ = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
	return mainSponge
}

func checkFirstSumcheckOfFirstRound(mainSponge *keccakSponge.Digest, circuit *Circuit, api frontend.API) {
	mainSponge.Absorb(circuit.First_OOD_Answer)
	initialCombinationRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
	plugInEvaluation := api.Add(
		typeConverters.LittleEndian(api, circuit.First_OOD_Answer),
		api.Mul(initialCombinationRandomness, circuit.Evaluation),
	)
	checkSumOverBool(api, plugInEvaluation, circuit.SumcheckPolysAsEvals[0])
}

func evaluateFunction(api frontend.API, evaluationsAsBytes [][]frontend.Variable, point frontend.Variable) (ans frontend.Variable) {
	evaluations := typeConverters.LittleEndianArr(api, evaluationsAsBytes)
	inv2 := api.Inverse(2)
	b0 := evaluations[0]
	b1 := api.Mul(api.Add(api.Neg(evaluations[2]), api.Mul(4, evaluations[1]), api.Mul(-3, evaluations[0])), inv2)
	b2 := api.Mul(api.Add(evaluations[2], api.Mul(-2, evaluations[1]), evaluations[0]), inv2)
	return api.Add(api.Mul(point, point, b2), api.Mul(point, b1), b0)
}

func checkSumOverBool(api frontend.API, value frontend.Variable, polyEvals [][]frontend.Variable) {
	sumOverBools := api.Add(
		typeConverters.LittleEndian(api, polyEvals[0]),
		typeConverters.LittleEndian(api, polyEvals[1]),
	)
	api.AssertIsEqual(value, sumOverBools)
}

func initialSumcheck(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest) {
	checkFirstSumcheckOfFirstRound(mainSponge, circuit, api)
	mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
	foldingRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
	for i := 1; i < circuit.FoldingParameter; i++ {
		randEval := evaluateFunction(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness)
		checkSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
		mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
		foldingRandomness = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
	}
}

func (circuit *Circuit) Define(api frontend.API) error {
	mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
	initialSumcheck(api, circuit, mainSponge)
	// api.AssertIsEqual(foldingRandomness2, 0)
	return nil
}

type KeccakDigest struct {
	KeccakDigest [32]uint8
}

type Fp256 struct {
	Limbs [4]uint64
}

type MultiPath[Digest any] struct {
	LeafSiblingHashes      []Digest
	AuthPathsPrefixLengths []uint64
	AuthPathsSuffixes      [][]Digest
	LeafIndexes            []uint64
}

type ProofElement struct {
	A MultiPath[KeccakDigest]
	B [][]Fp256
}

func main() {
	f, err := os.Open("../whir/proof")
	if err != nil {
		fmt.Println(err)
		return
	}
	defer f.Close()
	var x []ProofElement
	_, err = go_ark_serialize.CanonicalDeserializeWithMode(f, &x, false, false)

	verify_circuit(x)
}
