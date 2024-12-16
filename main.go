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

	IOPat := "🌪\ufe0f\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S1initial_combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S7stir_queries\u0000S3pow_queries\u0000A8pow-nonce\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A2final_coeffs\u0000S4final_queries\u0000S3pow_queries\u0000A8pow-nonce\u0000A3sumcheck_poly\u0000S1folding_randomness"
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(IOPat))
	fmt.Printf("io: %s\n", io.PPrint())

	transcriptBytes := [688]byte{110, 211, 95, 239, 223, 215, 8, 132, 125, 44, 231, 116, 26, 217, 204, 232, 167, 18, 76, 66, 184, 91, 20, 145, 109, 127, 62, 47, 114, 255, 32, 4, 97, 231, 74, 31, 22, 179, 54, 104, 230, 65, 227, 215, 50, 254, 8, 65, 253, 183, 24, 213, 132, 235, 161, 165, 215, 148, 8, 202, 232, 155, 225, 10, 27, 86, 149, 12, 132, 5, 141, 142, 175, 232, 220, 5, 178, 31, 48, 163, 46, 156, 30, 90, 239, 227, 163, 195, 96, 181, 125, 126, 68, 29, 164, 26, 71, 145, 181, 2, 38, 163, 139, 29, 200, 201, 191, 75, 201, 198, 12, 198, 43, 116, 123, 252, 75, 77, 78, 154, 160, 127, 188, 44, 23, 205, 161, 32, 200, 106, 149, 164, 180, 163, 24, 228, 28, 181, 155, 93, 148, 6, 65, 10, 215, 172, 120, 43, 42, 180, 248, 53, 239, 38, 149, 144, 242, 187, 131, 39, 152, 161, 136, 247, 39, 175, 146, 200, 166, 204, 24, 98, 30, 13, 67, 215, 137, 193, 63, 240, 165, 174, 68, 202, 32, 84, 153, 79, 137, 215, 151, 46, 251, 62, 32, 193, 4, 221, 82, 154, 204, 252, 173, 83, 37, 63, 146, 150, 46, 80, 216, 50, 72, 95, 64, 63, 66, 233, 243, 36, 35, 213, 25, 38, 179, 131, 29, 133, 137, 237, 136, 132, 246, 202, 71, 133, 48, 229, 116, 180, 110, 1, 64, 2, 172, 222, 71, 151, 242, 21, 249, 24, 28, 242, 204, 32, 148, 16, 48, 206, 38, 93, 120, 22, 233, 197, 171, 195, 119, 54, 178, 192, 84, 117, 152, 42, 240, 210, 70, 43, 252, 227, 222, 226, 73, 147, 8, 37, 76, 29, 104, 79, 59, 66, 45, 71, 159, 106, 166, 90, 223, 124, 251, 41, 71, 161, 168, 175, 200, 107, 187, 7, 7, 69, 202, 195, 120, 132, 204, 22, 0, 0, 0, 0, 0, 0, 0, 19, 3, 138, 250, 164, 68, 86, 9, 8, 58, 66, 236, 24, 194, 47, 182, 154, 42, 76, 170, 126, 54, 206, 123, 74, 127, 20, 180, 46, 190, 101, 127, 29, 229, 25, 6, 5, 252, 191, 168, 85, 157, 215, 12, 49, 9, 207, 30, 111, 139, 121, 129, 21, 200, 108, 42, 252, 86, 186, 22, 124, 229, 55, 169, 6, 7, 214, 36, 32, 59, 110, 74, 186, 165, 95, 166, 149, 143, 166, 243, 59, 99, 171, 58, 81, 248, 210, 232, 47, 52, 152, 164, 214, 164, 76, 64, 31, 104, 125, 2, 184, 78, 132, 201, 39, 2, 122, 103, 137, 19, 24, 16, 190, 84, 246, 132, 96, 60, 167, 211, 131, 121, 129, 193, 44, 79, 91, 193, 4, 7, 178, 63, 12, 188, 2, 191, 153, 47, 138, 7, 118, 185, 16, 189, 92, 28, 177, 193, 149, 235, 163, 215, 61, 212, 16, 104, 215, 179, 58, 70, 32, 176, 18, 15, 91, 30, 102, 77, 234, 203, 206, 142, 73, 119, 215, 222, 65, 84, 252, 67, 7, 225, 31, 23, 198, 82, 35, 174, 165, 102, 72, 209, 47, 68, 180, 178, 211, 154, 231, 207, 227, 120, 135, 79, 221, 19, 67, 246, 124, 177, 241, 102, 130, 105, 200, 215, 52, 78, 76, 20, 63, 23, 252, 2, 44, 192, 85, 116, 251, 143, 187, 149, 252, 45, 22, 90, 80, 254, 167, 106, 127, 36, 162, 86, 177, 73, 114, 137, 182, 120, 247, 69, 94, 159, 227, 105, 0, 0, 0, 0, 0, 0, 0, 0, 11, 96, 17, 161, 233, 103, 115, 162, 15, 69, 38, 207, 4, 205, 99, 204, 92, 226, 151, 121, 108, 1, 227, 14, 151, 114, 239, 38, 226, 27, 14, 57, 39, 108, 252, 233, 145, 124, 97, 18, 74, 143, 12, 145, 3, 206, 202, 215, 163, 192, 209, 78, 184, 138, 96, 252, 21, 197, 31, 244, 173, 218, 28, 54, 8, 59, 10, 110, 20, 143, 247, 226, 219, 130, 250, 158, 64, 222, 102, 82, 144, 199, 50, 128, 3, 1, 93, 197, 94, 245, 107, 190, 166, 83, 4, 96, 3}
	println(len(transcriptBytes))
	transcript := [688]uints.U8{}

	for i := range transcriptBytes {
		transcript[i] = uints.NewU8(transcriptBytes[i])
	}

	verify_circuit(x, IOPat, transcript)
}
