package hashmanager

import (
	"github.com/consensys/gnark/frontend"
	"github.com/vocdoni/gnark-crypto-primitives/poseidon"
)

type HashManager struct {
	poseidonInstance poseidon.Poseidon
	HashCollector    []frontend.Variable
	api              frontend.API
}

func NewHashManager(api frontend.API) *HashManager {
	manager := new(HashManager)
	manager.poseidonInstance = poseidon.NewPoseidon(api)
	manager.HashCollector = []frontend.Variable{}
	return manager
}

func (manager *HashManager) WriteInput(inputs ...frontend.Variable) {
	manager.poseidonInstance.Write(inputs...)
}

func (manager *HashManager) WriteInputAndCollectAndReturnHash(inputs ...frontend.Variable) frontend.Variable {
	manager.poseidonInstance.Write(inputs...)
	hashUntilNow := manager.poseidonInstance.Sum()
	// manager.HashCollector = append(manager.HashCollector, hashUntilNow)
	// manager.poseidonInstance.Write(hashUntilNow)
	manager.poseidonInstance.Reset()
	return hashUntilNow
}
