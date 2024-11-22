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
		bytes[i] = uint8(num >> (8 * i) & 0xFF)
	}
	return bytes
}

func verify_circuit(proofs []ProofElement, roots []KeccakDigest) {

	for i := range proofs {
		// i := 0
		var numOfLeavesProved = len(proofs[i].A.LeafIndexes)
		var treeHeight = len(proofs[i].A.AuthPathsSuffixes[0])

		var authPaths = make([][][]uints.U8, numOfLeavesProved)

		// println(i)
		// println(numOfLeavesProved)
		// println("proof len", len(proofs))
		// println(treeHeight)
		// fmt.Println(proofs[i].A)
		// fmt.Println(proofs[i].B)
		var leaves = make([][]uints.U8, numOfLeavesProved)
		var leaf_sibling_hashes = make([][]uints.U8, numOfLeavesProved)

		for j := 0; j < numOfLeavesProved; j++ {
			authPaths[j] = make([][]uints.U8, treeHeight)

			for z := 0; z < treeHeight; z++ {
				authPaths[j][z] = make([]uints.U8, 32)
			}
			leaves[j] = make([]uints.U8, 136)
			leaf_sibling_hashes[j] = make([]uints.U8, 32)
		}

		var leaf_indexes = make([]uints.U8, numOfLeavesProved)

		var root_hash = make([]uints.U8, 32)

		var circuit = VerifyMerkleProofCircuit{
			Leaves:            leaves,
			LeafIndexes:       leaf_indexes,
			LeafSiblingHashes: leaf_sibling_hashes,
			AuthPaths:         authPaths,
			RootHash:          root_hash,
		}

		ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
		pk, vk, _ := groth16.Setup(ccs)

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

		for z := range numOfLeavesProved {
			leaf_sibling_hashes[z] = uints.NewU8Array(proofs[i].A.LeafSiblingHashes[z].KeccakDigest[:])
			leaf_indexes[z] = uints.NewU8(uint8(proofs[i].A.LeafIndexes[z]))
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

		assignment := VerifyMerkleProofCircuit{
			Leaves:            leaves,
			LeafIndexes:       leaf_indexes,
			LeafSiblingHashes: leaf_sibling_hashes,
			AuthPaths:         authPaths,
			RootHash:          uints.NewU8Array(roots[i].KeccakDigest[:]),
		}

		witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
		publicWitness, _ := witness.Public()
		proof, _ := groth16.Prove(ccs, pk, witness)
		groth16.Verify(proof, vk, publicWitness)
	}
}
