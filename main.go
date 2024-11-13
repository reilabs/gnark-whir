package main

import (
    "github.com/consensys/gnark-crypto/ecc"
    "github.com/consensys/gnark/backend/groth16"
    "github.com/consensys/gnark/frontend"
    "github.com/consensys/gnark/frontend/cs/r1cs"
    "reilabs/whir-verifier-circuit/keccakSponge"
    "reilabs/whir-verifier-circuit/utilities"
    "encoding/json"
    "io/ioutil"
    // "strconv"
    "os"
    "fmt"
)

type Circuit struct {
    ClaimedEvaluation  frontend.Variable `gnark:"Supposed evaluation for the Verifier query"`
    IOPattern []frontend.Variable `gnark:"Input output pattern for the protocol. Used to seed the initial sponge"` 
    MerkleRoots [][]frontend.Variable `gnark:"Merkle roots of the initial and folded codes"` 
    OODEvaluations [][]frontend.Variable `gnark:"Out-of-domain query evaluations"` 
	SumcheckPolysAsEvals [][][]frontend.Variable `gnark:"Quadratic sumcheck polynomials in their evaluation form (Evaluated over 0, 1, 2)"`
    FoldingParameter int
    NumberOfRounds int
    Nonce []frontend.Variable
    Answers [][][]frontend.Variable
    FinalCoeffs []frontend.Variable
}

func initializeSpongeWithIOPatternAndMerkleRoot (circuit *Circuit, api frontend.API) *keccakSponge.Digest {
    helperSponge, _ := keccakSponge.NewKeccak(api)
	helperSponge.Absorb(circuit.IOPattern)
	mainSponge, _ := keccakSponge.NewKeccakWithTag(api, helperSponge.Squeeze(32))
    mainSponge.Absorb(circuit.MerkleRoots[0])
    _ = utilities.BigEndian(api, mainSponge.Squeeze(47))
    return mainSponge
}

func checkTheVeryFirstSumcheck (mainSponge *keccakSponge.Digest, circuit *Circuit, api frontend.API) {
    mainSponge.Absorb(circuit.OODEvaluations[0])
    initialCombinationRandomness := utilities.BigEndian(api, mainSponge.Squeeze(47))
    plugInEvaluation := api.Add(
        utilities.LittleEndian(api, circuit.OODEvaluations[0]), 
        api.Mul(initialCombinationRandomness, circuit.ClaimedEvaluation),
    )
    utilities.CheckSumOverBool(api, plugInEvaluation, circuit.SumcheckPolysAsEvals[0])
}


func initialSumchecks(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest) (foldingRandomness []frontend.Variable) {
    checkTheVeryFirstSumcheck(mainSponge, circuit, api)
    mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
    foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))
    for i := 1; i < circuit.FoldingParameter; i++ {
        randEval := utilities.QuadraticUnivarPolyFromEvaluations(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness[len(foldingRandomness)-1])
        utilities.CheckSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
        mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
        foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))
    }
    return foldingRandomness;
}

func firstSumcheckOfARound(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest, foldingRandomness []frontend.Variable) {
    combinationRandomness := utilities.BigEndian(api, mainSponge.Squeeze(47))
    prevPolynEvalAtFoldingRandomness := utilities.QuadraticUnivarPolyFromEvaluations(api, circuit.SumcheckPolysAsEvals[1], foldingRandomness[len(foldingRandomness)-1])
    OODandStirChallengeAnswers := []frontend.Variable{utilities.LittleEndian(api, circuit.OODEvaluations[1])}
    for i := range circuit.Answers[0] {
        OODandStirChallengeAnswers = append(OODandStirChallengeAnswers, utilities.MultivarPoly(circuit.Answers[0][i], foldingRandomness, api))
    }
    addedPart := utilities.UnivarPoly(api, OODandStirChallengeAnswers, combinationRandomness)
    supposedSum := api.Add(prevPolynEvalAtFoldingRandomness, addedPart)
    utilities.CheckSumOverBool(api, supposedSum, circuit.SumcheckPolysAsEvals[2])
}

func checkMainRounds(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest, foldingRandomness []frontend.Variable) {
    //This should be in a for loop
    mainSponge.Absorb(circuit.MerkleRoots[1])
    mainSponge.Squeeze(47) // OODQuery
    mainSponge.Absorb(circuit.OODEvaluations[1])
    mainSponge.Squeeze(32) // Stir Queries Seed
    mainSponge.Squeeze(32) // Proof of Work queries
    mainSponge.Absorb(circuit.Nonce)
    firstSumcheckOfARound(api, circuit, mainSponge, foldingRandomness)
    
    mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[2])
    foldingRandomness = []frontend.Variable{}
    foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))
    
    for i := 1; i < circuit.FoldingParameter; i++ {
        randEval := utilities.QuadraticUnivarPolyFromEvaluations(api, circuit.SumcheckPolysAsEvals[2 + i-1], foldingRandomness[len(foldingRandomness)-1])
        utilities.CheckSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[2 + i])
        mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[2 + i])
        foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))
    }

    // Checks in line 512-522 is omitted for now as we need to swap out the ChaCha part. Here is a sketch of what we need to do
        // var finalFolds []frontend.Variable
        // for i := range circuit.Answers[1] {
            // finalFolds = append(finalFolds, utilities.MultivarPoly(circuit.Answers[1][i], foldingRandomness, api))
        // }
        // finalEvaluations = [Use ChaCha to create random indexes. Use these to get random field elements and evaluate the final polynomial on these random field elements.]
        // Check if finalFolds == finalEvaluations

    api.AssertIsEqual(utilities.LittleEndian(api, circuit.FinalCoeffs), utilities.MultivarPoly(circuit.Answers[1][0], foldingRandomness, api))
}

func (circuit *Circuit) Define(api frontend.API) error {
    mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
    foldingRandomness := initialSumchecks(api, circuit, mainSponge)
    checkMainRounds(api, circuit, mainSponge, foldingRandomness)
    return nil
}

type ProofTranscript struct {
    ClaimedEvaluation string `json:"ClaimedEvaluation"`
	PolynomialsAsEvaluations [][][]uint8 `json:"PolynomialsAsEvaluations"`
    OODEvaluations [][]uint8 `json:"OODEvaluations"`
    MerkleRoots [][]uint8 `json:"MerkleRoots"`
    Nonce []uint8 `json:"Nonce"`
    IOPattern []uint8 `json:"IOPattern"`
    FinalCoeffs []uint8 `json:"FinalCoeffs"`
    Answers [][][]string `json:"Answers"`
}

func strToVar (str string) frontend.Variable {
    return frontend.Variable(utilities.NewBigIntFromString(str))
}

func strArrToVarArr(strArr []string) []frontend.Variable {
    var ans []frontend.Variable
    for _, v := range strArr {
        ans = append(ans, strToVar(v))
    }
    return ans;
}

func str2DArrToVar2DArr(str2DArr [][]string) [][]frontend.Variable {
    var ans [][]frontend.Variable
    for i := range str2DArr {
        ans = append(ans, strArrToVarArr(str2DArr[i]))
    }
    return ans;
}

func byte2DArrToVar2DArr(byte2DArr [][]uint8) [][]frontend.Variable {
    var ans [][]frontend.Variable
    for i := range byte2DArr {
        ans = append(ans, utilities.ByteArrToVarArr(byte2DArr[i]))
    }
    return ans;
}

func str3DArrToVar3DArr(str3DArr [][][]string) [][][]frontend.Variable {
    var ans [][][]frontend.Variable
    for i := range str3DArr {
        ans = append(ans, str2DArrToVar2DArr(str3DArr[i]))
    }
    return ans;
}

func byte3DArrToVar3DArr(byte3DArr [][][]uint8) [][][]frontend.Variable {
    var ans [][][]frontend.Variable
    for i := range byte3DArr {
        ans = append(ans, byte2DArrToVar2DArr(byte3DArr[i]))
    }
    return ans;
}

func main() {
    jsonFile, err := os.Open("proofTranscript.json")
    if err != nil {
        fmt.Println(err)
    }
    defer jsonFile.Close()
    byteValue, _ := ioutil.ReadAll(jsonFile)    
    var proofTranscript ProofTranscript
    json.Unmarshal(byteValue, &proofTranscript)

    claimedEvaluation := strToVar(proofTranscript.ClaimedEvaluation)
    iopattern := utilities.ByteArrToVarArr(proofTranscript.IOPattern)
    merkleRoots := byte2DArrToVar2DArr(proofTranscript.MerkleRoots)
    oodEvaluations := byte2DArrToVar2DArr(proofTranscript.OODEvaluations)
    polyEvals := byte3DArrToVar3DArr(proofTranscript.PolynomialsAsEvaluations)
    finalCoeffs := utilities.ByteArrToVarArr(proofTranscript.FinalCoeffs)
    nonce := utilities.ByteArrToVarArr(proofTranscript.Nonce)
    answers := str3DArrToVar3DArr(proofTranscript.Answers)

    var circuit = Circuit{
        IOPattern: make([]frontend.Variable, len(iopattern)),
        MerkleRoots: [][]frontend.Variable{
            make([]frontend.Variable, len(merkleRoots[0])),
            make([]frontend.Variable, len(merkleRoots[1])),
        },
        OODEvaluations: [][]frontend.Variable{
            make([]frontend.Variable, len(oodEvaluations[0])),
            make([]frontend.Variable, len(oodEvaluations[1])),
        },
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
            [][]frontend.Variable{
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
        FoldingParameter: 2,
        Nonce: make([]frontend.Variable, len(nonce)),
        Answers: [][][]frontend.Variable{
            [][]frontend.Variable{
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
            },
            [][]frontend.Variable{
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
                make([]frontend.Variable, 4),
            },
        },
        FinalCoeffs: make([]frontend.Variable, len(finalCoeffs)),
    }

    ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
    pk, vk, _ := groth16.Setup(ccs)
    
    assignment := Circuit{
        ClaimedEvaluation: claimedEvaluation, 
        IOPattern: iopattern,
        MerkleRoots: merkleRoots,
        OODEvaluations: oodEvaluations,
		SumcheckPolysAsEvals: polyEvals,
        FoldingParameter: 2,
        Nonce: nonce,
        Answers: answers,
        FinalCoeffs: finalCoeffs,
    }

    witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
    publicWitness, _ := witness.Public()
    proof, _ := groth16.Prove(ccs, pk, witness)
    groth16.Verify(proof, vk, publicWitness)
}


