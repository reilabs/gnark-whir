package main

import (
	"math/big"
	"tutorial/sumcheck-verifier-circuit/hashmanager"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

type VerifyMerkleProofCircuit struct {
	// Inputs
	Leaves            []frontend.Variable
	LeafIndexes       []frontend.Variable
	LeafSiblingHashes []frontend.Variable
	AuthPaths         [][]frontend.Variable
	// Public Input
	RootHash frontend.Variable `gnark:",public"`
}

func (circuit *VerifyMerkleProofCircuit) Define(api frontend.API) error {
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

func main() {
	var number_of_variables = 2

	var authPaths = make([][]frontend.Variable, number_of_variables)
	for i := 0; i < number_of_variables; i++ {
		authPaths[i] = make([]frontend.Variable, 3)
	}

	var leaves = make([]frontend.Variable, 3)
	var leaf_indexes = make([]frontend.Variable, 3)
	var leaf_sibling_hashes = make([]frontend.Variable, 3)
	var root_hash = big.NewInt(1)

	var circuit = VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       leaf_indexes,
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths:         authPaths,
		RootHash:          root_hash,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	assignment := VerifyMerkleProofCircuit{
		Leaves:            leaves,
		LeafIndexes:       leaf_indexes,
		LeafSiblingHashes: leaf_sibling_hashes,
		AuthPaths:         authPaths,
		RootHash:          root_hash,
	}
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness)
	groth16.Verify(proof, vk, publicWitness)
}
