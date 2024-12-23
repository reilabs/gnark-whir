package main

import (
	"fmt"
	"os"

	"github.com/consensys/gnark/std/math/uints"
	gnark_nimue "github.com/reilabs/gnark-nimue"
	go_ark_serialize "github.com/reilabs/go-ark-serialize"
)

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

	IOPat := "🌪\ufe0f\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S1initial_combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S20stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S10stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S7stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S5stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S4stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S4stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S3stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S2stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S2stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S2stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1merkle_digest\u0000S1ood_query\u0000A1ood_ans\u0000S2stir_queries\u0000S1combination_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A3sumcheck_poly\u0000S1folding_randomness\u0000A1final_coeffs\u0000S2final_queries"
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(IOPat))
	fmt.Printf("io: %s\n", io.PPrint())

	transcriptBytes := [3104]byte{102, 86, 13, 145, 45, 154, 193, 188, 95, 145, 88, 85, 23, 207, 239, 72, 94, 210, 148, 75, 83, 30, 137, 59, 150, 186, 10, 211, 130, 30, 28, 34, 249, 119, 239, 182, 212, 126, 27, 244, 169, 49, 119, 15, 183, 249, 30, 219, 188, 107, 241, 111, 239, 226, 249, 236, 66, 160, 117, 26, 140, 210, 187, 15, 177, 19, 109, 221, 199, 142, 107, 216, 109, 79, 212, 52, 53, 21, 157, 230, 128, 193, 6, 200, 244, 116, 175, 253, 108, 176, 71, 53, 101, 208, 43, 33, 73, 100, 130, 201, 160, 229, 145, 95, 205, 82, 92, 84, 202, 204, 181, 28, 153, 2, 108, 41, 177, 179, 154, 167, 255, 143, 95, 198, 153, 80, 244, 30, 228, 228, 193, 163, 249, 26, 108, 45, 147, 72, 117, 137, 204, 183, 81, 225, 22, 66, 39, 227, 196, 20, 135, 144, 192, 74, 96, 95, 214, 157, 251, 15, 226, 223, 34, 156, 42, 227, 178, 114, 224, 59, 38, 149, 218, 118, 53, 194, 254, 131, 160, 105, 170, 144, 105, 130, 105, 2, 244, 34, 242, 141, 54, 36, 125, 230, 158, 214, 246, 196, 29, 250, 40, 52, 84, 234, 1, 183, 14, 223, 148, 133, 129, 202, 214, 218, 239, 104, 47, 248, 62, 153, 104, 17, 234, 22, 241, 88, 107, 209, 5, 85, 240, 9, 126, 222, 22, 38, 235, 221, 9, 193, 159, 183, 171, 233, 161, 145, 97, 131, 251, 175, 227, 225, 157, 6, 216, 28, 251, 191, 61, 3, 111, 231, 97, 8, 74, 183, 166, 136, 215, 174, 238, 246, 115, 138, 176, 193, 124, 248, 23, 82, 145, 238, 65, 164, 95, 100, 205, 22, 117, 92, 36, 36, 167, 152, 129, 164, 153, 136, 146, 2, 183, 249, 34, 168, 125, 133, 156, 198, 206, 45, 29, 179, 149, 232, 64, 164, 98, 140, 179, 5, 131, 170, 48, 36, 78, 124, 103, 160, 8, 41, 205, 63, 119, 122, 17, 171, 80, 182, 194, 197, 14, 47, 234, 105, 94, 30, 128, 137, 92, 159, 144, 11, 146, 16, 160, 206, 2, 249, 191, 184, 87, 113, 141, 95, 250, 235, 14, 194, 233, 30, 22, 128, 19, 94, 232, 132, 104, 136, 248, 139, 59, 87, 120, 33, 20, 185, 173, 180, 210, 61, 137, 111, 40, 116, 140, 192, 165, 103, 172, 187, 229, 2, 102, 141, 13, 78, 59, 241, 127, 111, 8, 166, 215, 109, 36, 38, 217, 72, 226, 243, 97, 213, 1, 119, 140, 209, 214, 214, 135, 8, 115, 42, 32, 64, 156, 231, 38, 207, 31, 41, 15, 161, 142, 237, 164, 17, 143, 18, 51, 137, 211, 121, 231, 221, 83, 175, 53, 163, 224, 125, 197, 14, 245, 173, 3, 241, 144, 250, 104, 93, 160, 223, 202, 129, 110, 4, 239, 80, 143, 4, 149, 86, 177, 218, 47, 206, 204, 46, 109, 90, 136, 79, 82, 18, 229, 113, 113, 226, 180, 55, 231, 159, 43, 86, 222, 121, 137, 124, 152, 81, 113, 12, 170, 20, 58, 77, 113, 150, 60, 49, 150, 47, 82, 239, 150, 251, 129, 191, 86, 33, 243, 21, 255, 121, 217, 83, 224, 253, 154, 185, 233, 181, 214, 7, 120, 204, 61, 223, 236, 123, 149, 9, 3, 161, 22, 180, 83, 112, 108, 67, 143, 54, 180, 81, 6, 164, 88, 0, 137, 176, 46, 56, 148, 152, 189, 28, 136, 251, 204, 80, 248, 182, 10, 93, 35, 105, 81, 1, 65, 102, 239, 174, 124, 99, 168, 240, 142, 215, 93, 166, 251, 245, 244, 115, 123, 53, 166, 1, 101, 59, 149, 243, 248, 229, 164, 254, 179, 124, 169, 175, 217, 181, 110, 60, 253, 247, 84, 150, 27, 155, 111, 176, 100, 158, 30, 81, 142, 240, 27, 1, 22, 55, 183, 170, 85, 118, 179, 249, 29, 107, 184, 242, 245, 253, 181, 152, 165, 122, 66, 132, 209, 38, 82, 202, 142, 42, 212, 33, 115, 62, 181, 39, 84, 115, 166, 170, 148, 253, 128, 243, 2, 145, 78, 89, 28, 226, 71, 190, 190, 226, 203, 8, 80, 243, 123, 165, 87, 133, 116, 150, 212, 76, 233, 38, 68, 48, 22, 227, 55, 40, 227, 104, 68, 237, 4, 164, 94, 201, 50, 197, 7, 226, 215, 41, 227, 174, 185, 42, 121, 220, 109, 150, 65, 170, 78, 3, 70, 162, 195, 189, 197, 116, 63, 123, 97, 190, 54, 24, 62, 171, 157, 224, 189, 244, 129, 196, 192, 206, 139, 90, 12, 71, 56, 239, 66, 68, 136, 34, 102, 221, 76, 193, 253, 209, 220, 124, 95, 122, 188, 58, 62, 123, 230, 55, 7, 32, 140, 126, 150, 71, 246, 196, 224, 233, 202, 78, 100, 177, 174, 28, 105, 206, 97, 142, 189, 88, 171, 229, 217, 37, 255, 129, 143, 137, 21, 58, 249, 42, 113, 233, 35, 169, 227, 223, 238, 141, 46, 70, 16, 1, 224, 43, 163, 46, 148, 141, 160, 202, 34, 114, 68, 46, 122, 174, 214, 119, 161, 68, 254, 120, 131, 223, 38, 48, 118, 179, 24, 20, 192, 30, 136, 96, 57, 15, 224, 15, 240, 92, 254, 127, 174, 66, 82, 55, 141, 90, 125, 54, 50, 223, 209, 207, 122, 101, 159, 244, 107, 96, 27, 41, 38, 206, 239, 18, 205, 5, 230, 55, 107, 2, 157, 13, 238, 212, 193, 235, 215, 131, 16, 116, 204, 150, 124, 137, 99, 202, 160, 153, 40, 59, 111, 95, 86, 114, 185, 181, 234, 47, 153, 152, 129, 104, 194, 58, 54, 189, 62, 113, 135, 199, 161, 171, 44, 160, 132, 230, 67, 31, 204, 122, 138, 108, 154, 61, 219, 28, 76, 111, 56, 46, 134, 31, 66, 150, 26, 122, 79, 253, 117, 189, 107, 241, 221, 109, 45, 49, 173, 109, 101, 16, 96, 45, 95, 86, 77, 143, 113, 78, 156, 138, 245, 2, 226, 48, 150, 16, 147, 232, 34, 5, 211, 135, 107, 42, 180, 164, 161, 151, 194, 50, 255, 62, 79, 236, 247, 88, 36, 39, 170, 203, 64, 93, 221, 29, 72, 0, 75, 205, 161, 228, 203, 148, 71, 104, 82, 144, 184, 2, 39, 225, 148, 228, 141, 73, 131, 252, 250, 236, 166, 68, 50, 115, 178, 180, 126, 21, 104, 22, 194, 169, 214, 165, 26, 0, 165, 121, 61, 103, 227, 38, 193, 70, 139, 228, 253, 80, 108, 108, 59, 119, 65, 40, 58, 135, 126, 21, 197, 40, 14, 121, 196, 91, 212, 161, 69, 133, 3, 89, 179, 185, 237, 156, 88, 227, 121, 206, 2, 147, 127, 21, 232, 136, 175, 121, 255, 152, 8, 150, 73, 33, 90, 114, 232, 92, 219, 72, 185, 241, 199, 142, 79, 94, 255, 229, 190, 84, 102, 66, 123, 253, 151, 217, 192, 155, 16, 206, 209, 194, 37, 216, 158, 9, 37, 131, 45, 240, 252, 107, 164, 78, 221, 10, 79, 154, 155, 183, 118, 15, 192, 115, 3, 215, 147, 176, 247, 100, 69, 198, 121, 3, 203, 106, 116, 17, 71, 9, 212, 65, 192, 116, 114, 44, 74, 77, 150, 24, 149, 89, 135, 4, 219, 206, 57, 140, 7, 240, 188, 18, 215, 4, 44, 43, 234, 190, 39, 19, 87, 33, 53, 154, 239, 151, 96, 58, 83, 108, 248, 225, 16, 63, 95, 154, 224, 241, 195, 88, 91, 30, 144, 90, 128, 90, 34, 77, 246, 116, 121, 0, 243, 170, 216, 206, 222, 152, 2, 198, 62, 255, 246, 194, 108, 164, 249, 31, 70, 102, 138, 85, 128, 8, 14, 156, 210, 68, 224, 167, 34, 162, 19, 13, 24, 252, 18, 30, 154, 188, 127, 56, 146, 208, 157, 124, 138, 68, 88, 71, 216, 130, 89, 83, 36, 184, 211, 188, 17, 24, 140, 51, 220, 134, 43, 2, 165, 203, 19, 55, 128, 60, 14, 70, 36, 80, 130, 145, 213, 246, 5, 22, 230, 183, 204, 211, 229, 205, 175, 19, 72, 52, 50, 96, 103, 60, 148, 10, 228, 1, 251, 99, 246, 15, 197, 4, 91, 15, 182, 51, 2, 49, 91, 218, 207, 251, 182, 81, 25, 162, 220, 116, 245, 111, 40, 16, 107, 146, 41, 46, 183, 221, 40, 101, 15, 200, 164, 184, 222, 179, 244, 189, 144, 181, 240, 185, 62, 221, 237, 12, 19, 167, 6, 241, 211, 141, 14, 239, 206, 173, 112, 46, 72, 168, 234, 168, 129, 25, 61, 246, 160, 138, 240, 214, 29, 205, 127, 34, 7, 246, 49, 102, 89, 203, 60, 194, 68, 121, 87, 171, 165, 19, 49, 27, 154, 132, 237, 240, 204, 95, 107, 32, 153, 58, 125, 185, 159, 26, 208, 38, 223, 34, 131, 37, 116, 228, 68, 120, 146, 177, 161, 42, 182, 115, 218, 29, 130, 194, 191, 227, 107, 188, 161, 88, 146, 145, 52, 184, 100, 230, 183, 63, 37, 34, 8, 72, 198, 11, 137, 135, 142, 147, 72, 9, 92, 222, 197, 1, 201, 47, 209, 70, 102, 80, 89, 151, 150, 184, 20, 86, 12, 104, 106, 148, 101, 26, 228, 158, 90, 145, 176, 44, 4, 84, 204, 111, 90, 130, 96, 46, 142, 194, 103, 109, 18, 86, 202, 235, 166, 224, 124, 56, 234, 100, 221, 70, 221, 203, 70, 122, 240, 65, 149, 226, 90, 77, 243, 154, 55, 117, 176, 35, 244, 244, 242, 206, 204, 38, 23, 79, 127, 85, 125, 1, 137, 141, 119, 163, 151, 211, 95, 152, 209, 198, 207, 10, 90, 48, 127, 77, 111, 46, 72, 16, 133, 146, 233, 248, 190, 255, 164, 185, 217, 172, 73, 29, 211, 116, 12, 252, 102, 23, 41, 101, 24, 195, 44, 172, 62, 170, 105, 15, 130, 156, 192, 1, 162, 73, 15, 252, 113, 12, 244, 100, 174, 135, 206, 245, 96, 192, 5, 120, 72, 57, 42, 173, 221, 19, 158, 246, 150, 160, 111, 248, 9, 205, 71, 19, 218, 249, 141, 153, 88, 185, 252, 67, 208, 20, 58, 10, 19, 191, 213, 76, 170, 225, 14, 254, 56, 103, 158, 190, 7, 202, 10, 118, 26, 52, 253, 44, 213, 4, 241, 157, 245, 150, 12, 195, 148, 153, 191, 133, 188, 72, 235, 63, 47, 3, 110, 85, 197, 214, 163, 44, 50, 168, 190, 178, 63, 83, 142, 0, 15, 167, 121, 201, 9, 179, 53, 18, 185, 251, 22, 165, 94, 171, 24, 232, 8, 241, 0, 1, 8, 220, 247, 218, 248, 215, 249, 216, 116, 252, 150, 31, 123, 246, 143, 207, 189, 43, 134, 98, 97, 8, 204, 90, 250, 224, 188, 80, 195, 60, 38, 12, 249, 38, 190, 54, 88, 240, 158, 250, 115, 60, 238, 24, 118, 214, 142, 137, 34, 255, 215, 67, 109, 195, 221, 175, 35, 42, 67, 65, 178, 28, 89, 215, 41, 27, 249, 133, 109, 146, 215, 175, 128, 238, 31, 1, 4, 227, 222, 237, 47, 19, 187, 73, 210, 70, 228, 143, 18, 19, 124, 13, 3, 109, 25, 242, 10, 109, 254, 186, 134, 66, 219, 168, 57, 218, 215, 12, 87, 221, 26, 6, 131, 235, 104, 147, 128, 134, 8, 206, 126, 223, 41, 225, 240, 213, 30, 48, 103, 61, 55, 213, 13, 240, 63, 141, 130, 244, 68, 8, 98, 50, 170, 86, 232, 54, 139, 130, 18, 166, 218, 214, 41, 212, 232, 205, 124, 140, 250, 194, 73, 255, 93, 206, 38, 88, 203, 19, 225, 73, 127, 23, 245, 71, 20, 164, 107, 2, 53, 127, 72, 38, 154, 33, 141, 75, 210, 129, 90, 115, 192, 8, 200, 180, 234, 222, 150, 227, 82, 155, 165, 56, 60, 42, 154, 36, 237, 20, 101, 139, 218, 15, 163, 12, 140, 150, 40, 54, 54, 115, 27, 164, 63, 210, 37, 199, 135, 10, 170, 67, 190, 191, 86, 196, 184, 27, 106, 122, 18, 206, 20, 45, 54, 69, 180, 169, 44, 24, 6, 28, 165, 102, 77, 198, 248, 64, 212, 105, 225, 132, 133, 18, 217, 38, 133, 114, 80, 29, 132, 223, 32, 233, 25, 27, 185, 82, 72, 90, 141, 113, 31, 132, 214, 135, 84, 79, 212, 236, 201, 42, 4, 108, 134, 65, 7, 154, 210, 16, 151, 32, 33, 174, 37, 133, 159, 184, 240, 33, 138, 77, 48, 109, 154, 203, 173, 250, 66, 49, 51, 246, 117, 203, 29, 103, 140, 115, 126, 190, 75, 96, 79, 42, 21, 182, 235, 181, 133, 91, 141, 74, 211, 119, 173, 209, 44, 112, 218, 152, 4, 79, 38, 236, 159, 76, 122, 2, 136, 248, 7, 186, 149, 116, 46, 4, 49, 254, 176, 91, 120, 64, 69, 177, 144, 251, 206, 106, 101, 69, 72, 122, 16, 248, 72, 44, 77, 191, 4, 224, 148, 251, 109, 87, 114, 39, 212, 31, 1, 246, 248, 228, 248, 158, 94, 213, 3, 34, 176, 145, 19, 3, 156, 17, 184, 185, 23, 82, 121, 78, 214, 178, 108, 20, 97, 214, 117, 141, 205, 1, 181, 99, 112, 97, 177, 241, 124, 83, 70, 29, 161, 105, 177, 152, 251, 17, 102, 147, 115, 225, 112, 42, 128, 21, 42, 226, 106, 166, 32, 116, 250, 12, 202, 20, 159, 124, 157, 152, 161, 147, 253, 0, 9, 2, 55, 254, 139, 55, 225, 61, 123, 48, 39, 181, 47, 27, 84, 183, 76, 33, 25, 24, 42, 24, 204, 10, 116, 124, 4, 141, 10, 35, 227, 139, 155, 115, 203, 21, 49, 247, 97, 210, 52, 218, 32, 54, 45, 87, 119, 63, 19, 40, 238, 252, 173, 34, 108, 49, 112, 78, 28, 118, 98, 213, 79, 34, 92, 235, 87, 23, 219, 33, 62, 175, 71, 132, 24, 27, 118, 218, 248, 116, 169, 106, 54, 137, 120, 6, 0, 14, 16, 126, 99, 40, 64, 82, 213, 171, 146, 163, 34, 223, 15, 3, 146, 210, 141, 178, 54, 161, 1, 30, 234, 239, 12, 99, 14, 238, 161, 3, 199, 200, 47, 85, 90, 214, 75, 38, 5, 245, 98, 13, 35, 242, 64, 150, 241, 189, 8, 37, 14, 247, 9, 52, 166, 253, 126, 210, 44, 82, 116, 28, 38, 25, 103, 87, 182, 114, 203, 59, 12, 64, 182, 229, 136, 59, 140, 219, 251, 162, 79, 161, 28, 252, 134, 171, 183, 172, 106, 52, 39, 153, 254, 33, 226, 27, 192, 55, 119, 235, 168, 176, 234, 45, 86, 157, 73, 224, 0, 5, 118, 196, 13, 35, 62, 147, 79, 210, 204, 222, 41, 212, 205, 119, 114, 20, 85, 175, 94, 23, 247, 181, 21, 49, 252, 144, 186, 61, 72, 135, 87, 44, 131, 91, 52, 105, 169, 68, 57, 166, 173, 224, 52, 240, 229, 196, 49, 7, 238, 20, 77, 161, 74, 129, 225, 82, 195, 21, 218, 129, 130, 206, 196, 95, 181, 229, 80, 5, 207, 181, 123, 51, 53, 83, 171, 113, 121, 90, 132, 7, 145, 1, 0, 42, 240, 221, 139, 202, 5, 153, 75, 54, 177, 50, 89, 6, 9, 19, 198, 101, 6, 20, 211, 174, 36, 78, 21, 238, 86, 229, 218, 29, 84, 250, 189, 235, 86, 36, 15, 233, 93, 94, 102, 31, 110, 130, 77, 188, 190, 110, 86, 18, 132, 191, 121, 179, 53, 208, 49, 139, 35, 95, 130, 40, 199, 233, 14, 122, 24, 37, 153, 14, 125, 158, 7, 174, 18, 84, 52, 212, 14, 124, 168, 97, 72, 125, 152, 65, 215, 71, 103, 165, 73, 107, 25, 19, 192, 240, 99, 77, 49, 64, 180, 170, 134, 17, 172, 84, 126, 184, 182, 189, 230, 204, 166, 20, 211, 184, 79, 17, 67, 44, 190, 190, 193, 2, 58, 8, 158, 253, 64, 95, 183, 104, 183, 55, 181, 114, 248, 189, 110, 134, 164, 46, 139, 248, 211, 121, 100, 163, 109, 160, 20, 2, 208, 132, 64, 4, 17, 33, 211, 51, 119, 236, 111, 27, 192, 143, 11, 14, 42, 76, 208, 126, 251, 13, 115, 197, 168, 94, 54, 153, 180, 170, 230, 87, 179, 144, 121, 23, 51, 0, 27, 14, 22, 155, 109, 113, 168, 175, 230, 116, 167, 39, 146, 2, 118, 127, 155, 19, 169, 113, 253, 113, 114, 178, 187, 99, 129, 168, 117, 225, 111, 13, 37, 197, 94, 154, 136, 9, 4, 2, 197, 60, 81, 180, 91, 90, 209, 12, 136, 173, 97, 25, 212, 105, 73, 180, 93, 40, 243, 5, 155, 46, 238, 9, 213, 207, 27, 195, 121, 116, 96, 53, 100, 251, 254, 177, 68, 133, 80, 72, 137, 80, 194, 85, 128, 6, 170, 109, 33, 232, 72, 205, 193, 185, 236, 4, 142, 168, 178, 17, 223, 81, 75, 231, 178, 180, 15, 242, 48, 73, 25, 109, 178, 182, 82, 52, 113, 160, 59, 81, 53, 243, 71, 125, 179, 251, 64, 0, 217, 22, 227, 247, 139, 235, 162, 180, 108, 123, 205, 89, 165, 126, 195, 128, 107, 197, 211, 182, 109, 16, 57, 163, 191, 6, 188, 231, 50, 243, 82, 1, 194, 157, 195, 241, 241, 149, 231, 245, 209, 227, 23, 191, 225, 101, 30, 160, 202, 113, 24, 216, 128, 254, 172, 100, 126, 248, 11, 3, 141, 233, 81, 41, 25, 19, 217, 209, 183, 134, 30, 17, 95, 14, 195, 149, 153, 127, 51, 56, 189, 68, 111, 161, 129, 246, 54, 57, 184, 3, 44, 45, 10, 131, 59, 13, 130, 206, 137, 91, 41, 35, 83, 195, 157, 53, 67, 18, 209, 199, 198, 65, 196, 114, 245, 198, 163, 191, 1, 189, 156, 243, 41, 209, 110, 226, 115, 5, 128, 175, 172, 102, 155, 93, 120, 244, 251, 246, 126, 188, 136, 57, 170, 133, 4, 196, 242, 181, 205, 111, 130, 136, 87, 8, 202, 107, 136, 7, 3, 38, 223, 130, 231, 243, 209, 177, 139, 92, 238, 126, 237, 167, 207, 22, 106, 57, 125, 72, 14, 119, 1, 29, 243, 244, 0, 66, 75, 192, 83, 120, 175, 42, 7, 235, 186, 10, 43, 214, 17, 70, 157, 97, 57, 90, 17, 251, 28, 67, 223, 193, 198, 234, 252, 31, 164, 43, 129, 182, 160, 220, 0, 232, 176, 23, 98, 40, 196, 183, 133, 198, 233, 0, 138, 182, 87, 141, 151, 181, 40, 72, 23, 145, 166, 43, 183, 7, 84, 177, 131, 46, 184, 178, 61, 175, 0, 6, 101, 180, 79, 30, 221, 124, 129, 79, 3, 148, 232, 188, 48, 96, 145, 246, 234, 43, 18, 131, 24, 174, 201, 188, 185, 95, 84, 54, 242, 246, 198, 28}
	transcript := [3104]uints.U8{}

	for i := range transcriptBytes {
		transcript[i] = uints.NewU8(transcriptBytes[i])
	}

	verify_circuit(x, IOPat, transcript)
}
