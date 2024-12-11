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

// func checkFirstSumcheckOfFirstRound(mainSponge *keccakSponge.Digest, circuit *Circuit, api frontend.API, firstOODAnswer []frontend.Variable) {
// 	initialCombinationRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
// 	plugInEvaluation := api.Add(
// 		typeConverters.LittleEndian(api, firstOODAnswer),
// 		api.Mul(initialCombinationRandomness, circuit.Evaluation),
// 	)
// 	checkSumOverBool(api, plugInEvaluation, circuit.SumcheckPolysAsEvals[0])
// }

// func evaluateFunction(api frontend.API, evaluationsAsBytes [][]frontend.Variable, point frontend.Variable) (ans frontend.Variable) {
// 	evaluations := typeConverters.LittleEndianArr(api, evaluationsAsBytes)
// 	inv2 := api.Inverse(2)
// 	b0 := evaluations[0]
// 	b1 := api.Mul(api.Add(api.Neg(evaluations[2]), api.Mul(4, evaluations[1]), api.Mul(-3, evaluations[0])), inv2)
// 	b2 := api.Mul(api.Add(evaluations[2], api.Mul(-2, evaluations[1]), evaluations[0]), inv2)
// 	return api.Add(api.Mul(point, point, b2), api.Mul(point, b1), b0)
// }

// func checkSumOverBool(api frontend.API, value frontend.Variable, polyEvals [][]frontend.Variable) {
// 	sumOverBools := api.Add(
// 		typeConverters.LittleEndian(api, polyEvals[0]),
// 		typeConverters.LittleEndian(api, polyEvals[1]),
// 	)
// 	api.AssertIsEqual(value, sumOverBools)
// }

// func initialSumcheck(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest) {
// 	checkFirstSumcheckOfFirstRound(mainSponge, circuit, api, circuit.First_OOD_Answer)
// 	mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
// 	foldingRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
// 	for i := 1; i < circuit.FoldingParameter; i++ {
// 		randEval := evaluateFunction(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness)
// 		checkSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
// 		mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
// 		foldingRandomness = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
// 	}
// }

// func (circuit *Circuit) Define(api frontend.API) error {
// 	mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
// 	initialSumcheck(api, circuit, mainSponge)
// 	// api.AssertIsEqual(foldingRandomness2, 0)
// 	return nil
// }

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

	IOPat := "🌪\ufe0f\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S47initial_combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S98stir_queries\u0000S32pow_queries\u0000A8pow-nonce\u0000S47combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A32final_coeffs\u0000S49final_queries\u0000S32pow_queries\u0000A8pow-nonce"
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(IOPat))
	fmt.Printf("io: %s\n", io.PPrint())

	transcriptBytes := [560]byte{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52, 105, 71, 149, 53, 62, 144, 224, 192, 219, 167, 236, 236, 224, 105, 226, 98, 87, 82, 121, 13, 4, 18, 49, 178, 124, 243, 213, 118, 68, 117, 148, 5, 10, 16, 206, 141, 126, 21, 229, 50, 53, 163, 110, 179, 54, 45, 161, 120, 46, 148, 122, 7, 195, 241, 88, 145, 84, 103, 81, 36, 207, 169, 138, 29, 96, 55, 199, 151, 83, 112, 221, 209, 55, 117, 55, 179, 242, 36, 117, 18, 134, 22, 128, 135, 247, 101, 40, 217, 81, 44, 182, 51, 232, 25, 110, 24, 241, 199, 179, 136, 76, 140, 108, 179, 53, 114, 136, 56, 154, 155, 190, 189, 47, 62, 144, 208, 251, 105, 93, 92, 221, 203, 166, 214, 112, 147, 45, 42, 249, 19, 0, 31, 219, 54, 118, 104, 157, 178, 135, 224, 247, 183, 238, 234, 234, 222, 200, 125, 23, 247, 222, 44, 16, 65, 246, 212, 255, 7, 8, 37, 101, 82, 102, 200, 124, 173, 229, 19, 184, 163, 135, 70, 238, 23, 185, 7, 31, 122, 224, 43, 143, 173, 146, 81, 114, 214, 9, 58, 245, 96, 197, 16, 231, 154, 107, 181, 14, 12, 105, 0, 19, 199, 234, 168, 62, 196, 26, 208, 190, 241, 38, 83, 160, 138, 156, 187, 0, 87, 125, 176, 47, 126, 193, 35, 159, 234, 6, 100, 144, 175, 225, 182, 73, 73, 120, 151, 30, 173, 71, 77, 205, 95, 198, 143, 141, 13, 73, 147, 145, 208, 241, 167, 97, 106, 116, 76, 157, 60, 190, 126, 248, 215, 141, 33, 194, 44, 251, 56, 197, 2, 204, 30, 31, 212, 74, 48, 246, 16, 139, 204, 233, 6, 190, 248, 88, 175, 223, 23, 0, 0, 0, 0, 0, 0, 0, 2, 28, 5, 63, 131, 42, 196, 63, 138, 40, 255, 128, 127, 13, 234, 165, 234, 87, 3, 187, 228, 103, 75, 9, 204, 222, 58, 248, 176, 252, 44, 36, 30, 153, 78, 197, 116, 235, 200, 206, 162, 205, 123, 71, 105, 186, 122, 203, 168, 157, 239, 120, 234, 162, 54, 18, 152, 39, 100, 232, 188, 18, 164, 13, 47, 148, 242, 155, 111, 208, 94, 88, 138, 250, 185, 207, 38, 96, 53, 232, 172, 89, 152, 237, 207, 16, 82, 204, 142, 19, 50, 202, 58, 91, 205, 237, 13, 46, 85, 130, 12, 41, 188, 173, 79, 118, 18, 149, 214, 18, 60, 43, 234, 74, 168, 131, 94, 69, 13, 184, 68, 211, 65, 130, 95, 178, 143, 114, 1, 146, 81, 38, 127, 149, 233, 5, 98, 95, 197, 159, 197, 26, 113, 232, 236, 119, 125, 38, 145, 140, 108, 125, 43, 215, 76, 99, 101, 0, 231, 137, 5, 26, 140, 244, 90, 185, 138, 134, 226, 172, 175, 182, 203, 19, 225, 29, 231, 139, 167, 22, 7, 156, 209, 66, 36, 73, 100, 91, 121, 103, 99, 176, 46, 96, 90, 39, 215, 204, 237, 228, 147, 202, 22, 87, 85, 14, 211, 133, 159, 7, 92, 63, 233, 92, 155, 196, 204, 100, 105, 204, 195, 26, 183, 14, 3, 0, 0, 0, 0, 0, 0, 0, 2}
	println(len(transcriptBytes))
	transcript := [560]uints.U8{}

	for i := range transcriptBytes {
		transcript[i] = uints.NewU8(transcriptBytes[i])
	}

	verify_circuit(x, IOPat, transcript)
}
