package main

import (
	"fmt"
	"os"
	"reilabs/whir-verifier-circuit/keccakSponge"
	"reilabs/whir-verifier-circuit/typeConverters"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/uints"
	gnark_nimue "github.com/reilabs/gnark-nimue"
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

	var roots = []KeccakDigest{{[32]uint8{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52}},
		{[32]uint8{58, 107, 66, 235, 56, 51, 242, 113, 19, 161, 88, 169, 3, 19, 148, 198, 203, 99, 180, 237, 215, 227, 237, 177, 254, 215, 105, 94, 32, 218, 14, 48}}}

	IOPat := "🌪\ufe0f\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S47initial_combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S32stir_queries_seed\u0000S32pow_queries\u0000A8pow-nonce\u0000S47combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A32final_coeffs\u0000S32final_queries_seed\u0000S32pow_queries\u0000A8pow-nonce"
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(IOPat))
	fmt.Printf("io: %s\n", io.PPrint())

	transcriptBytes := [560]byte{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52, 34, 222, 231, 144, 26, 1, 111, 94, 211, 208, 9, 123, 2, 128, 115, 36, 22, 167, 134, 143, 221, 216, 151, 218, 157, 62, 24, 220, 237, 200, 176, 1, 10, 143, 212, 116, 96, 10, 226, 127, 95, 1, 246, 48, 167, 203, 62, 162, 81, 180, 163, 21, 86, 15, 90, 210, 104, 41, 43, 65, 57, 97, 216, 2, 16, 231, 231, 70, 86, 121, 22, 112, 238, 188, 214, 38, 191, 177, 218, 217, 15, 87, 199, 194, 137, 196, 39, 204, 50, 144, 170, 76, 4, 153, 217, 34, 178, 27, 127, 170, 216, 180, 22, 55, 14, 6, 94, 105, 187, 199, 27, 167, 68, 211, 132, 158, 3, 200, 53, 1, 134, 230, 255, 21, 71, 71, 70, 9, 220, 96, 19, 56, 152, 181, 63, 207, 103, 60, 8, 100, 22, 1, 165, 98, 58, 118, 96, 154, 94, 6, 165, 169, 236, 169, 193, 213, 102, 44, 138, 37, 42, 18, 253, 161, 116, 205, 150, 65, 85, 51, 244, 44, 181, 126, 51, 166, 64, 126, 159, 24, 100, 48, 60, 148, 63, 110, 25, 189, 178, 25, 46, 10, 239, 220, 57, 83, 59, 170, 35, 30, 164, 22, 107, 209, 226, 133, 13, 162, 187, 58, 81, 13, 197, 190, 41, 227, 201, 76, 169, 60, 177, 33, 113, 30, 58, 107, 66, 235, 56, 51, 242, 113, 19, 161, 88, 169, 3, 19, 148, 198, 203, 99, 180, 237, 215, 227, 237, 177, 254, 215, 105, 94, 32, 218, 14, 48, 213, 6, 31, 254, 249, 36, 42, 55, 223, 187, 1, 200, 255, 121, 213, 241, 184, 70, 177, 234, 131, 195, 16, 25, 49, 76, 127, 234, 41, 200, 173, 33, 0, 0, 0, 0, 0, 0, 0, 2, 36, 222, 57, 96, 229, 182, 10, 156, 146, 55, 203, 10, 82, 150, 28, 253, 37, 43, 111, 27, 253, 252, 181, 176, 186, 121, 112, 152, 120, 141, 24, 37, 12, 47, 14, 59, 235, 21, 232, 226, 218, 29, 7, 100, 248, 68, 74, 178, 117, 144, 11, 219, 204, 99, 251, 255, 12, 155, 35, 161, 100, 174, 39, 42, 71, 31, 180, 191, 83, 21, 145, 10, 45, 19, 220, 74, 19, 157, 46, 255, 166, 91, 150, 109, 181, 133, 65, 80, 227, 51, 112, 165, 48, 48, 215, 13, 59, 236, 36, 56, 125, 180, 76, 198, 37, 46, 34, 229, 97, 255, 170, 111, 193, 205, 54, 216, 123, 235, 177, 86, 41, 39, 98, 242, 119, 73, 50, 19, 10, 221, 44, 149, 102, 6, 104, 25, 165, 116, 244, 56, 16, 60, 17, 15, 165, 69, 119, 175, 249, 156, 36, 153, 0, 21, 38, 110, 193, 159, 173, 24, 95, 94, 210, 193, 96, 32, 213, 9, 214, 221, 89, 45, 240, 231, 183, 178, 174, 251, 51, 234, 165, 195, 177, 24, 209, 118, 90, 81, 240, 129, 246, 39, 219, 191, 5, 3, 52, 60, 254, 232, 154, 225, 179, 221, 81, 92, 183, 236, 160, 47, 247, 170, 216, 89, 18, 10, 65, 123, 6, 176, 84, 145, 183, 24, 0, 0, 0, 0, 0, 0, 0, 5}
	println(len(transcriptBytes))
	transcript := [560]uints.U8{}

	for i := range transcriptBytes {
		transcript[i] = uints.NewU8(transcriptBytes[i])
	}
	// transcript := [560]uints.U8{uints.NewU8Array(transcriptBytes[:])}

	verify_circuit(x, roots, IOPat, transcript)
}
