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
	Leaves            []uints.U8
	LeafIndexes       []uints.U8
	LeafSiblingHashes []uints.U8
	AuthPaths         [][]uints.U8
	// Public Input
	RootHash []uints.U8 `gnark:",public"`
}

func (circuit *VerifyMerkleProofCircuit) Define(api frontend.API) error {
	keccak, _ := sha3.NewLegacyKeccak256(api)
	treeHeight := len(circuit.AuthPaths) + 1

	for i := 0; i < 1; i++ {
		leafIndex := api.ToBinary(circuit.LeafIndexes[i].Val, treeHeight)
		leafSiblingHash := circuit.LeafSiblingHashes

		keccak.Write(circuit.Leaves)
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

			siblingHash := circuit.AuthPaths[level-1]

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

	var authPaths = make([][]uints.U8, 2)

	authPaths[0] = uints.NewU8Array([]uint8{211, 51, 77, 19, 55, 238, 24, 9, 247, 114, 70, 103, 252, 66, 14, 208, 122, 205, 43, 196, 227, 79, 108, 84, 144, 71, 31, 6, 229, 129, 4, 168})
	authPaths[1] = uints.NewU8Array([]uint8{170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170, 170})

	var leaves = make([]uints.U8, 32)
	var leaf_indexes = make([]uints.U8, 1)
	var leaf_sibling_hashes = make([]uints.U8, 32)
	var root_hash = make([]uints.U8, 32)

	var circuit = VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       leaf_indexes,
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths: [][]uints.U8{
			make([]uints.U8, 32),
			make([]uints.U8, 32),
		},
		RootHash: root_hash,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	assignment := VerifyMerkleProofCircuit{
		Leaves:            uints.NewU8Array([]uint8{1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}),
		LeafIndexes:       []uints.U8{uints.NewU8(3)},
		LeafSiblingHashes: uints.NewU8Array([]uint8{224, 251, 63, 44, 19, 165, 111, 12, 78, 216, 36, 49, 48, 246, 150, 190, 11, 231, 70, 207, 250, 10, 210, 147, 126, 63, 41, 85, 118, 241, 15, 99}),
		AuthPaths:         authPaths,
		RootHash:          uints.NewU8Array([]uint8{156, 132, 156, 46, 222, 37, 3, 45, 120, 220, 18, 214, 60, 118, 81, 11, 158, 72, 24, 139, 222, 195, 77, 237, 222, 231, 48, 80, 29, 236, 143, 0}),
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness)
	groth16.Verify(proof, vk, publicWitness)
}
