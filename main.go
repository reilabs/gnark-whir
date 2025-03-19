package main

import (
	"encoding/json"
	"fmt"
	"log"
	"os"

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

type ProofObject struct {
	MerklePaths                  []ProofElement
	StatementValuesAtRandomPoint []Fp256
}

type Config struct {
	LogNumConstraints    int      `json:"log_num_constraints"`
	NRounds              int      `json:"n_rounds"`
	NVars                int      `json:"n_vars"`
	FoldingFactor        []int    `json:"folding_factor"`
	OODSamples           []int    `json:"ood_samples"`
	NumQueries           []int    `json:"num_queries"`
	PowBits              []int    `json:"pow_bits"`
	FinalQueries         int      `json:"final_queries"`
	FinalPowBits         int      `json:"final_pow_bits"`
	FinalFoldingPowBits  int      `json:"final_folding_pow_bits"`
	DomainGenerator      string   `json:"domain_generator"`
	Rate                 int      `json:"rate"`
	IOPattern            string   `json:"io_pattern"`
	Transcript           []byte   `json:"transcript"`
	TranscriptLen        int      `json:"transcript_len"`
	StatementEvaluations []string `json:"statement_evaluations"`
}

func main() {
	f, err := os.Open("../ProveKit/prover/proof")
	if err != nil {
		fmt.Println(err)
		return
	}
	defer f.Close()

	params, err := os.ReadFile("../ProveKit/prover/params")
	if err != nil {
		fmt.Println(err)
		return
	}

	var cfg Config
	if err := json.Unmarshal(params, &cfg); err != nil {
		log.Fatalf("Error unmarshalling JSON: %v\n", err)
	}

	fmt.Printf("Parsed configuration:\n%+v\n", cfg)

	var x ProofObject
	_, err = go_ark_serialize.CanonicalDeserializeWithMode(f, &x, false, false)
	if err != nil {
		fmt.Println(err)
		return
	}

	fmt.Println(x.StatementValuesAtRandomPoint)
	io := gnark_nimue.IOPattern{}
	_ = io.Parse([]byte(cfg.IOPattern))
	fmt.Printf("io: %s\n", io.PPrint())

	verify_circuit(x, cfg)
}
