package main

import (
	"fmt"

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

func prefixDecodePath[T any](prevPath []T, prefixLen uint64, suffix []T) []T {
	if prefixLen == 0 {
		res := make([]T, len(suffix))
		copy(res, suffix)
		return res
	} else {
		res := make([]T, prefixLen+uint64(len(suffix)))
		copy(res, prevPath[:prefixLen])
		copy(res[prefixLen:], suffix)
		return res
	}
}

func reverse[T any](s []T) []T {
	res := make([]T, len(s))
	copy(res, s)
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		res[i], res[j] = s[j], s[i]
	}
	return res
}

func toLittleEndianBytes(num uint64) []uint8 {
	bytes := make([]uint8, 8)
	for i := 0; i < 8; i++ {
		bytes[i] = uint8(num >> (8 * i) & 0xFF) // Extract each byte
	}
	return bytes
}

func verify_circuit(proofs []ProofElement) {
	// for i := range proofs {
	i := 0
	var numOfLeavesProved = 2
	var treeHeight = len(proofs[i].A.AuthPathsSuffixes[0])

	var authPaths = make([][][]uints.U8, numOfLeavesProved)

	println(i)
	println(numOfLeavesProved)
	for j := 0; j < numOfLeavesProved; j++ {
		authPaths[j] = make([][]uints.U8, treeHeight)
	}
	var authPathsTemp = make([][]KeccakDigest, numOfLeavesProved)
	var prevPath = proofs[i].A.AuthPathsSuffixes[0]
	authPathsTemp[0] = reverse(prevPath)

	for j := 0; j < len(authPaths[0]); j++ {
		authPaths[0][j] = uints.NewU8Array(authPathsTemp[0][j].KeccakDigest[:])
	}

	for j := 1; j < numOfLeavesProved; j++ {
		prevPath = prefixDecodePath(prevPath, proofs[i].A.AuthPathsPrefixLengths[j], proofs[i].A.AuthPathsSuffixes[j])
		authPathsTemp[j] = reverse(prevPath)
		for z := 0; z < treeHeight; z++ {
			authPaths[j][z] = uints.NewU8Array(authPathsTemp[j][z].KeccakDigest[:])
		}
	}

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

	for j := 0; j < numOfLeavesProved; j++ {
		fmt.Println(proofs[i].A.LeafSiblingHashes[j].KeccakDigest[:])
		leaf_sibling_hashes[j] = uints.NewU8Array(proofs[i].A.LeafSiblingHashes[j].KeccakDigest[:])
		leaf_indexes[j] = uints.NewU8(uint8(proofs[i].A.LeafIndexes[j]))
		fmt.Println(proofs[i].B[j])
	}

	for z := range numOfLeavesProved {
		big_output := make([]uint8, 136)
		copy(big_output[0:8], toLittleEndianBytes(4))

		for j := range proofs[i].B[z] {
			input := proofs[i].B[z][j]
			output := make([]uint8, 4*8)

			for i, num := range input.Limbs {
				serialized := toLittleEndianBytes(num)
				copy(output[i*8:(i+1)*8], serialized)
			}
			copy(big_output[j*32+8:(j+1)*32+8], output)
		}
		leaves[z] = uints.NewU8Array(big_output)
	}

	// leaf_sibling_hashes[0] = uints.NewU8Array([]uint8{193, 13, 183, 152, 249, 32, 72, 69, 254, 130, 132, 51, 181, 111, 143, 200, 6, 210, 97, 0, 43, 145, 81, 96, 50, 28, 138, 188, 200, 17, 91, 181})
	// leaf_sibling_hashes[1] = uints.NewU8Array([]uint8{121, 181, 105, 15, 9, 169, 235, 69, 109, 178, 75, 230, 203, 40, 219, 154, 63, 128, 89, 249, 147, 67, 183, 172, 89, 171, 109, 198, 185, 183, 195, 2})

	assignment := VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       leaf_indexes,
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths:         authPaths,
		RootHash:          uints.NewU8Array([]uint8{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52}),
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness)
	groth16.Verify(proof, vk, publicWitness)
	// }
}
