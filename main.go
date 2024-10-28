package main

import (
    "math/big"
    "github.com/consensys/gnark-crypto/ecc"
    "github.com/consensys/gnark/backend/groth16"
    "github.com/consensys/gnark/frontend"
    "github.com/consensys/gnark/frontend/cs/r1cs"
    "reilabs/whir-verifier-circuit/keccakSponge"
    "reilabs/whir-verifier-circuit/typeConverters"
)

type Circuit struct {
    IOPattern []frontend.Variable `gnark:"Input output pattern for the protocol. Used to seed the initial sponge"` 
    MerkleRoot []frontend.Variable `gnark:"Merkle root for the Reed-Solomon encoding of the polynomial"` 
    First_OOD_Answer []frontend.Variable `gnark:"First out-of-domain query answer"` 
    Evaluation  frontend.Variable `gnark:"Supposed evaluation for the Verifier query"`
	SumcheckPolysAsEvals [][][]frontend.Variable `gnark:"Quadratic sumcheck polynomials in their evaluation form (Evaluated over 0, 1, 2)"`
    FoldingParameter int
}

func initializeSpongeWithIOPatternAndMerkleRoot (circuit *Circuit, api frontend.API) *keccakSponge.Digest {
    helperSponge, _ := keccakSponge.NewKeccak(api)
	helperSponge.Absorb(circuit.IOPattern)
	mainSponge, _ := keccakSponge.NewKeccakWithTag(api, helperSponge.Squeeze(32))
    mainSponge.Absorb(circuit.MerkleRoot)
    _ = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    return mainSponge
}

func checkFirstSumcheckOfFirstRound (mainSponge *keccakSponge.Digest, circuit *Circuit, api frontend.API) {
    mainSponge.Absorb(circuit.First_OOD_Answer)
    initialCombinationRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    plugInEvaluation := api.Add(
        typeConverters.LittleEndian(api, circuit.First_OOD_Answer), 
        api.Mul(initialCombinationRandomness, circuit.Evaluation),
    )
    checkSumOverBool(api, plugInEvaluation, circuit.SumcheckPolysAsEvals[0])
}

func evaluateFunction(api frontend.API, evaluationsAsBytes [][]frontend.Variable, point frontend.Variable) (ans frontend.Variable) {
    evaluations := typeConverters.LittleEndianArr(api, evaluationsAsBytes)
    inv2 := api.Inverse(2)
    b0 := evaluations[0]
    b1 := api.Mul(api.Add(api.Neg(evaluations[2]), api.Mul(4, evaluations[1]), api.Mul(-3, evaluations[0])), inv2)
    b2 := api.Mul(api.Add(evaluations[2],api.Mul(-2, evaluations[1]), evaluations[0]), inv2)
    return api.Add(api.Mul(point, point, b2), api.Mul(point, b1), b0)
}

func checkSumOverBool (api frontend.API, value frontend.Variable, polyEvals [][]frontend.Variable) {
    sumOverBools := api.Add(
        typeConverters.LittleEndian(api, polyEvals[0]), 
        typeConverters.LittleEndian(api, polyEvals[1]),
    )
    api.AssertIsEqual(value, sumOverBools)
}

func initialSumcheck(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest) {
    checkFirstSumcheckOfFirstRound(mainSponge, circuit, api)
    mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
    foldingRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    for i := 1; i < circuit.FoldingParameter; i++ {
        randEval := evaluateFunction(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness)
        checkSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
        mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
        foldingRandomness = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    }
}

func (circuit *Circuit) Define(api frontend.API) error {
    mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
    initialSumcheck(api, circuit, mainSponge)
    // api.AssertIsEqual(foldingRandomness2, 0)
    return nil
}


func main() {
    iopattern := typeConverters.ByteArrToVarArr([]uint8{240, 159, 140, 170, 239, 184, 143, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 52, 55, 105, 110, 105, 116, 105, 97, 108, 95, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 51, 50, 115, 116, 105, 114, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101, 0, 83, 52, 55, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 102, 105, 110, 97, 108, 95, 99, 111, 101, 102, 102, 115, 0, 83, 51, 50, 102, 105, 110, 97, 108, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101})
    merkleRoot := typeConverters.ByteArrToVarArr([]uint8{91, 191, 10, 79, 160, 14, 48, 231, 9, 136, 174, 237, 91, 33, 107, 115, 61, 110, 60, 253, 34, 13, 138, 139, 134, 177, 20, 13, 47, 236, 192, 235})
    ood_answer := typeConverters.ByteArrToVarArr([]uint8{4, 27, 46, 84, 196, 191, 23, 182, 251, 220, 156, 128, 85, 238, 179, 56, 241, 254, 128, 107, 179, 72, 236, 44, 74, 87, 108, 154, 134, 218, 53, 46})
    evaluation, _ := new(big.Int).SetString("120", 10)
    polyEvals := make([][][]frontend.Variable, 2)
    
    polyEvals[0] = make([][]frontend.Variable, 3)
    polyEvals[0][0] = typeConverters.ByteArrToVarArr([]uint8{234, 189, 202, 54, 254, 88, 189, 252, 248, 56, 103, 9, 240, 34, 51, 53, 126, 240, 161, 15, 102, 232, 227, 162, 20, 171, 67, 203, 28, 187, 7, 35})
    polyEvals[0][1] = typeConverters.ByteArrToVarArr([]uint8{122, 188, 153, 3, 135, 248, 158, 26, 251, 56, 179, 32, 27, 103, 127, 18, 95, 129, 84, 119, 107, 228, 43, 122, 196, 145, 177, 118, 228, 95, 204, 16})
    polyEvals[0][2] = typeConverters.ByteArrToVarArr([]uint8{56, 72, 87, 174, 9, 109, 239, 51, 172, 233, 60, 234, 229, 97, 191, 86, 153, 135, 143, 195, 24, 128, 27, 138, 31, 222, 138, 101, 13, 168, 180, 24})
    
    polyEvals[1] = make([][]frontend.Variable, 3)
    polyEvals[1][0] = typeConverters.ByteArrToVarArr([]uint8{231, 75, 148, 173, 131, 39, 90, 195, 50, 11, 215, 81, 40, 61, 106, 172, 193, 66, 163, 254, 180, 87, 208, 152, 226, 131, 238, 244, 156, 197, 182, 19})
    polyEvals[1][1] = typeConverters.ByteArrToVarArr([]uint8{64, 116, 125, 243, 22, 29, 240, 25, 207, 88, 133, 217, 154, 237, 11, 147, 97, 57, 19, 224, 98, 90, 212, 49, 72, 25, 155, 136, 17, 34, 83, 24})
    polyEvals[1][2] = typeConverters.ByteArrToVarArr([]uint8{126, 12, 163, 53, 95, 139, 201, 187, 180, 185, 12, 238, 250, 117, 239, 47, 202, 167, 3, 220, 87, 21, 182, 39, 144, 147, 76, 242, 46, 225, 0, 47})

    var circuit = Circuit{
        IOPattern: make([]frontend.Variable, len(iopattern)),
        MerkleRoot: make([]frontend.Variable, len(merkleRoot)),
        First_OOD_Answer: make([]frontend.Variable, len(ood_answer)),
		SumcheckPolysAsEvals: [][][]frontend.Variable{
            [][]frontend.Variable {
                make([]frontend.Variable, 32),
                make([]frontend.Variable, 32),
                make([]frontend.Variable, 32),
            },
            [][]frontend.Variable{
                make([]frontend.Variable, 32),
                make([]frontend.Variable, 32),
                make([]frontend.Variable, 32),
            },
        },
    }

    ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
    pk, vk, _ := groth16.Setup(ccs)
    
    assignment := Circuit{
        IOPattern: iopattern,
        MerkleRoot: merkleRoot,
        First_OOD_Answer: ood_answer,
        Evaluation: evaluation, 
		SumcheckPolysAsEvals: polyEvals,
        FoldingParameter: 2,
    }

    witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
    publicWitness, _ := witness.Public()
    proof, _ := groth16.Prove(ccs, pk, witness)
    groth16.Verify(proof, vk, publicWitness)
}


