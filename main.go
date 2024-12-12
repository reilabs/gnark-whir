package main

import (
	"fmt"
	"os"

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

	IOPat := "🌪\ufe0f\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S47initial_combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A32merkle_digest\u0000S47ood_query\u0000A32ood_ans\u0000S97stir_queries\u0000S32pow_queries\u0000A8pow-nonce\u0000S47combination_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A96sumcheck_poly\u0000S47folding_randomness\u0000A64final_coeffs\u0000S49final_queries\u0000S32pow_queries\u0000A8pow-nonce\u0000A96sumcheck_poly\u0000S47folding_randomness"
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(IOPat))
	fmt.Printf("io: %s\n", io.PPrint())

	transcriptBytes := [688]byte{20, 73, 22, 35, 151, 190, 200, 31, 82, 241, 219, 131, 37, 65, 199, 71, 35, 103, 244, 180, 95, 57, 12, 88, 150, 240, 130, 33, 169, 213, 157, 19, 87, 163, 148, 126, 140, 88, 197, 212, 188, 129, 23, 220, 46, 199, 151, 114, 223, 197, 223, 6, 169, 228, 161, 59, 69, 123, 142, 247, 77, 81, 186, 6, 133, 213, 238, 190, 187, 253, 113, 24, 62, 228, 19, 207, 110, 171, 67, 156, 118, 99, 146, 13, 254, 133, 226, 16, 146, 96, 53, 40, 92, 153, 116, 39, 211, 205, 165, 175, 100, 80, 53, 0, 16, 14, 189, 134, 8, 4, 136, 254, 197, 186, 206, 122, 97, 164, 15, 227, 220, 186, 138, 176, 100, 6, 170, 15, 196, 234, 177, 239, 19, 102, 227, 18, 183, 184, 49, 103, 154, 37, 183, 95, 216, 208, 238, 161, 25, 70, 121, 214, 28, 79, 87, 168, 212, 127, 38, 14, 133, 104, 209, 29, 250, 193, 243, 37, 179, 19, 214, 103, 16, 154, 102, 214, 59, 226, 147, 134, 28, 122, 250, 78, 191, 130, 55, 226, 48, 178, 230, 9, 219, 45, 169, 174, 79, 58, 59, 197, 9, 68, 166, 148, 243, 57, 192, 104, 125, 251, 211, 34, 73, 111, 65, 6, 198, 13, 45, 9, 107, 150, 70, 41, 221, 53, 72, 229, 13, 217, 182, 127, 171, 203, 70, 204, 0, 32, 57, 30, 185, 89, 102, 126, 232, 237, 50, 198, 92, 110, 12, 90, 173, 38, 246, 19, 225, 76, 186, 246, 248, 221, 226, 16, 124, 218, 253, 49, 186, 200, 11, 168, 110, 247, 235, 33, 25, 98, 207, 115, 93, 215, 12, 199, 131, 248, 170, 3, 21, 76, 40, 227, 117, 206, 60, 107, 85, 14, 57, 50, 14, 164, 126, 103, 145, 236, 66, 99, 125, 60, 178, 116, 166, 36, 148, 8, 242, 158, 170, 27, 0, 0, 0, 0, 0, 0, 0, 10, 232, 60, 136, 148, 57, 254, 71, 217, 205, 181, 115, 54, 79, 184, 57, 106, 95, 152, 24, 100, 115, 58, 225, 156, 147, 168, 190, 86, 217, 178, 2, 14, 70, 228, 29, 191, 110, 1, 120, 163, 67, 161, 65, 155, 172, 65, 157, 0, 224, 168, 63, 201, 241, 167, 234, 21, 109, 64, 69, 74, 253, 51, 20, 6, 157, 218, 229, 123, 229, 13, 7, 229, 235, 160, 132, 179, 98, 85, 36, 228, 5, 138, 58, 155, 140, 250, 224, 233, 173, 178, 21, 225, 9, 187, 206, 24, 147, 68, 31, 212, 103, 59, 61, 17, 34, 229, 20, 55, 56, 4, 76, 55, 94, 128, 167, 237, 157, 115, 209, 119, 82, 235, 54, 161, 244, 156, 30, 16, 200, 162, 24, 131, 167, 177, 1, 217, 144, 52, 72, 175, 222, 156, 101, 133, 121, 221, 57, 78, 66, 65, 238, 67, 130, 90, 227, 35, 65, 44, 206, 35, 226, 81, 213, 196, 136, 82, 86, 250, 4, 169, 212, 60, 109, 248, 58, 203, 206, 86, 53, 52, 17, 107, 2, 207, 4, 176, 244, 115, 19, 20, 126, 16, 154, 128, 211, 153, 25, 1, 132, 50, 152, 194, 84, 200, 161, 141, 131, 176, 3, 162, 232, 50, 48, 130, 35, 106, 194, 29, 24, 25, 145, 96, 62, 1, 0, 36, 112, 231, 118, 9, 36, 152, 86, 131, 121, 17, 143, 34, 132, 164, 40, 44, 172, 98, 75, 4, 67, 192, 218, 62, 176, 240, 1, 210, 253, 6, 0, 0, 0, 0, 0, 0, 0, 11, 220, 194, 197, 1, 206, 95, 45, 198, 151, 3, 150, 54, 0, 184, 19, 73, 187, 221, 54, 179, 104, 194, 200, 187, 18, 103, 94, 156, 142, 183, 247, 1, 225, 19, 237, 96, 115, 21, 185, 23, 131, 134, 47, 98, 213, 176, 95, 104, 80, 43, 58, 243, 166, 56, 118, 196, 248, 101, 35, 211, 123, 216, 142, 39, 36, 180, 226, 149, 250, 61, 204, 236, 123, 156, 119, 120, 12, 92, 8, 52, 148, 25, 123, 246, 66, 180, 165, 178, 194, 26, 187, 78, 163, 24, 211, 30}
	println(len(transcriptBytes))
	transcript := [688]uints.U8{}

	for i := range transcriptBytes {
		transcript[i] = uints.NewU8(transcriptBytes[i])
	}

	verify_circuit(x, IOPat, transcript)
}
