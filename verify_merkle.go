package main

import (
	"tutorial/sumcheck-verifier-circuit/hashmanager"

	"github.com/consensys/gnark/frontend"
)

type VerifyMerkleProofCircuit2 struct {
	// Inputs
	Leaves            []frontend.Variable
	LeafIndexes       []frontend.Variable
	LeafSiblingHashes []frontend.Variable
	AuthPaths         [][]frontend.Variable
	// Public Input
	RootHash frontend.Variable `gnark:",public"`
}

func (circuit *VerifyMerkleProofCircuit) Define2(api frontend.API) error {
	var manager = hashmanager.NewHashManager(api)
	numLeaves := len(circuit.Leaves)
	// ``treeHeight := len(circuit.AuthPathSuffixes[0]) + 2

	for i := 0; i < numLeaves; i++ {
		leaf := circuit.Leaves[i]
		leafIndex := circuit.LeafIndexes[i]
		leafSiblingHash := circuit.LeafSiblingHashes[i]

		authPath := circuit.AuthPaths[i]

		claimedLeafHash := manager.WriteInputAndCollectAndReturnHash(leaf)

		dir := api.And(leafIndex, 1)
		leftChild := api.Select(dir, leafSiblingHash, claimedLeafHash)
		rightChild := api.Select(dir, claimedLeafHash, leafSiblingHash)

		currentHash := manager.WriteInputAndCollectAndReturnHash(leftChild, rightChild)

		index := api.Div(leafIndex, 2)

		for level := 0; level < len(authPath); level++ {
			siblingHash := authPath[level]

			dir := api.And(index, 1)
			left := api.Select(dir, siblingHash, currentHash)
			right := api.Select(dir, currentHash, siblingHash)

			currentHash = manager.WriteInputAndCollectAndReturnHash(left, right)

			index = api.Div(index, 2)
		}

		api.AssertIsEqual(currentHash, circuit.RootHash)
	}

	return nil
}
