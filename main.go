package main

import (
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/hash/sha3"
	"github.com/consensys/gnark/std/math/uints"
)

type VerifyMerkleProofCircuit struct {
	// Inputs
	Leaves            [][]uints.U8
	LeafIndexes       []uints.U8
	LeafSiblingHashes [][]uints.U8
	AuthPaths         [][][]uints.U8
	// Public Input
	RootHash []uints.U8 `gnark:",public"`
}

func (circuit *VerifyMerkleProofCircuit) Define(api frontend.API) error {
	numOfLeavesProved := len(circuit.Leaves)

	for i := 0; i < numOfLeavesProved; i++ {
		treeHeight := len(circuit.AuthPaths[i]) + 1

		leafIndex := api.ToBinary(circuit.LeafIndexes[i].Val, treeHeight)
		leafSiblingHash := circuit.LeafSiblingHashes[i]
		keccak, _ := sha3.NewLegacyKeccak256(api)

		keccak.Write(circuit.Leaves[i])
		claimedLeafHash := keccak.Sum()
		dir := leafIndex[0]
		// api.Println(dir)

		x_leftChild := make([]uints.U8, 32)
		x_rightChild := make([]uints.U8, 32)

		for j := 0; j < 32; j++ {
			x_leftChild[j].Val = api.Select(dir, leafSiblingHash[j].Val, claimedLeafHash[j].Val)
			x_rightChild[j].Val = api.Select(dir, claimedLeafHash[j].Val, leafSiblingHash[j].Val)
		}

		// api.Println(x_leftChild)
		// api.Println(x_rightChild)
		keccak_new, _ := sha3.NewLegacyKeccak256(api)

		tmp := append(x_leftChild, x_rightChild...)
		keccak_new.Write(tmp)
		currentHash := keccak_new.Sum()

		// api.Println(currentHash)

		for level := 1; level < treeHeight; level++ {
			index := leafIndex[level]

			siblingHash := circuit.AuthPaths[i][level-1]

			dir := api.And(index, 1)
			left := make([]uints.U8, 32)
			right := make([]uints.U8, 32)

			for z := 0; z < 32; z++ {
				left[z].Val = api.Select(dir, siblingHash[z].Val, currentHash[z].Val)
				right[z].Val = api.Select(dir, currentHash[z].Val, siblingHash[z].Val)
			}

			// api.Println(left)
			// api.Println(right)

			new_tmp := append(left, right...)
			keccak, _ := sha3.NewLegacyKeccak256(api)
			keccak.Write(new_tmp)
			currentHash = keccak.Sum()
			// api.Println(currentHash)
		}

		for z := 0; z < 32; z++ {
			api.AssertIsEqual(currentHash[z].Val, circuit.RootHash[z].Val)
		}
	}

	return nil
}

func main() {

	var numOfLeavesProved = 2

	var authPaths = make([][][]uints.U8, numOfLeavesProved)
	authPaths[0] = make([][]uints.U8, 2)
	authPaths[0][0] = uints.NewU8Array([]uint8{210, 251, 227, 90, 167, 45, 18, 202, 115, 95, 12, 44, 121, 251, 100, 56, 10, 223, 89, 69, 229, 214, 221, 45, 154, 183, 246, 77, 110, 157, 230, 64})
	authPaths[0][1] = uints.NewU8Array([]uint8{172, 194, 50, 157, 236, 173, 136, 136, 253, 203, 140, 59, 202, 25, 15, 36, 77, 228, 212, 82, 43, 88, 169, 178, 85, 239, 40, 106, 240, 15, 188, 12})
	authPaths[1] = make([][]uints.U8, 2)
	authPaths[1][0] = uints.NewU8Array([]uint8{210, 251, 227, 90, 167, 45, 18, 202, 115, 95, 12, 44, 121, 251, 100, 56, 10, 223, 89, 69, 229, 214, 221, 45, 154, 183, 246, 77, 110, 157, 230, 64})
	authPaths[1][1] = uints.NewU8Array([]uint8{172, 194, 50, 157, 236, 173, 136, 136, 253, 203, 140, 59, 202, 25, 15, 36, 77, 228, 212, 82, 43, 88, 169, 178, 85, 239, 40, 106, 240, 15, 188, 12})

	var leaves = make([][]uints.U8, numOfLeavesProved)
	leaves[0] = make([]uints.U8, 136)
	leaves[1] = make([]uints.U8, 136)

	var leaf_indexes = make([]uints.U8, numOfLeavesProved)
	var leaf_sibling_hashes = make([][]uints.U8, numOfLeavesProved)
	leaf_sibling_hashes[0] = make([]uints.U8, 32)
	leaf_sibling_hashes[1] = make([]uints.U8, 32)
	var root_hash = make([]uints.U8, 32)

	var circuit = VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       leaf_indexes,
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths: [][][]uints.U8{
			{make([]uints.U8, 32), make([]uints.U8, 32)},
			{make([]uints.U8, 32), make([]uints.U8, 32)},
		},
		RootHash: root_hash,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	leaves[0] = uints.NewU8Array([]uint8{4, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0})
	leaves[1] = uints.NewU8Array([]uint8{4, 0, 0, 0, 0, 0, 0, 0, 102, 236, 198, 133, 51, 227, 164, 78, 21, 108, 201, 224, 129, 211, 86, 186, 163, 75, 216, 4, 23, 196, 38, 190, 125, 48, 197, 203, 153, 127, 17, 41, 128, 38, 59, 239, 27, 208, 110, 243, 146, 225, 121, 161, 161, 140, 202, 248, 53, 173, 101, 167, 4, 122, 114, 67, 25, 153, 220, 27, 247, 151, 213, 16, 155, 96, 175, 72, 152, 178, 26, 220, 161, 199, 227, 219, 9, 46, 114, 95, 37, 103, 116, 203, 168, 117, 14, 129, 222, 161, 37, 77, 199, 254, 253, 40, 181, 154, 35, 178, 128, 159, 228, 128, 31, 61, 148, 156, 41, 231, 229, 157, 183, 200, 1, 110, 150, 43, 90, 6, 122, 10, 61, 157, 36, 23, 194, 16})
	leaf_sibling_hashes[0] = uints.NewU8Array([]uint8{193, 13, 183, 152, 249, 32, 72, 69, 254, 130, 132, 51, 181, 111, 143, 200, 6, 210, 97, 0, 43, 145, 81, 96, 50, 28, 138, 188, 200, 17, 91, 181})
	leaf_sibling_hashes[1] = uints.NewU8Array([]uint8{121, 181, 105, 15, 9, 169, 235, 69, 109, 178, 75, 230, 203, 40, 219, 154, 63, 128, 89, 249, 147, 67, 183, 172, 89, 171, 109, 198, 185, 183, 195, 2})

	assignment := VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       []uints.U8{uints.NewU8(0), uints.NewU8(1)},
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths:         authPaths,
		RootHash:          uints.NewU8Array([]uint8{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52}),
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness)
	groth16.Verify(proof, vk, publicWitness)
}
