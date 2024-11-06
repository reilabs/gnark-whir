package main

import (
    "math/big"
    "github.com/consensys/gnark-crypto/ecc"
    "github.com/consensys/gnark/backend/groth16"
    "github.com/consensys/gnark/frontend"
    "github.com/consensys/gnark/frontend/cs/r1cs"
    "reilabs/whir-verifier-circuit/keccakSponge"
    "reilabs/whir-verifier-circuit/utilities"
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
    FinalCoeffs [][]frontend.Variable
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

    api.AssertIsEqual(utilities.LittleEndian(api, circuit.FinalCoeffs[0]), utilities.MultivarPoly(circuit.Answers[1][0], foldingRandomness, api))
}

func (circuit *Circuit) Define(api frontend.API) error {
    mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
    foldingRandomness := initialSumchecks(api, circuit, mainSponge)
    checkMainRounds(api, circuit, mainSponge, foldingRandomness)
    return nil
}

func main() {
    claimedEvaluation, _ := new(big.Int).SetString("120", 10)
    iopattern := utilities.ByteArrToVarArr([]uint8{240, 159, 140, 170, 239, 184, 143, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 52, 55, 105, 110, 105, 116, 105, 97, 108, 95, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 51, 50, 115, 116, 105, 114, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101, 0, 83, 52, 55, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 102, 105, 110, 97, 108, 95, 99, 111, 101, 102, 102, 115, 0, 83, 51, 50, 102, 105, 110, 97, 108, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101})
    merkleRoots := [][]frontend.Variable{
        utilities.ByteArrToVarArr([]uint8{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52}),
        utilities.ByteArrToVarArr([]uint8{58, 107, 66, 235, 56, 51, 242, 113, 19, 161, 88, 169, 3, 19, 148, 198, 203, 99, 180, 237, 215, 227, 237, 177, 254, 215, 105, 94, 32, 218, 14, 48}),
    }
    oodEvaluations := [][]frontend.Variable{
        utilities.ByteArrToVarArr([]uint8{34, 222, 231, 144, 26, 1, 111, 94, 211, 208, 9, 123, 2, 128, 115, 36, 22, 167, 134, 143, 221, 216, 151, 218, 157, 62, 24, 220, 237, 200, 176, 1}),
        utilities.ByteArrToVarArr([]uint8{213, 6, 31, 254, 249, 36, 42, 55, 223, 187, 1, 200, 255, 121, 213, 241, 184, 70, 177, 234, 131, 195, 16, 25, 49, 76, 127, 234, 41, 200, 173, 33}),
    }
    polyEvals := make([][][]frontend.Variable, 4)
    
    polyEvals[0] = make([][]frontend.Variable, 3)
    polyEvals[0][0] = utilities.ByteArrToVarArr([]uint8{10, 143, 212, 116, 96, 10, 226, 127, 95, 1, 246, 48, 167, 203, 62, 162, 81, 180, 163, 21, 86, 15, 90, 210, 104, 41, 43, 65, 57, 97, 216, 2})
    polyEvals[0][1] = utilities.ByteArrToVarArr([]uint8{16, 231, 231, 70, 86, 121, 22, 112, 238, 188, 214, 38, 191, 177, 218, 217, 15, 87, 199, 194, 137, 196, 39, 204, 50, 144, 170, 76, 4, 153, 217, 34})
    polyEvals[0][2] = utilities.ByteArrToVarArr([]uint8{178, 27, 127, 170, 216, 180, 22, 55, 14, 6, 94, 105, 187, 199, 27, 167, 68, 211, 132, 158, 3, 200, 53, 1, 134, 230, 255, 21, 71, 71, 70, 9})
    
    polyEvals[1] = make([][]frontend.Variable, 3)
    polyEvals[1][0] = utilities.ByteArrToVarArr([]uint8{220, 96, 19, 56, 152, 181, 63, 207, 103, 60, 8, 100, 22, 1, 165, 98, 58, 118, 96, 154, 94, 6, 165, 169, 236, 169, 193, 213, 102, 44, 138, 37})
    polyEvals[1][1] = utilities.ByteArrToVarArr([]uint8{42, 18, 253, 161, 116, 205, 150, 65, 85, 51, 244, 44, 181, 126, 51, 166, 64, 126, 159, 24, 100, 48, 60, 148, 63, 110, 25, 189, 178, 25, 46, 10})
    polyEvals[1][2] = utilities.ByteArrToVarArr([]uint8{239, 220, 57, 83, 59, 170, 35, 30, 164, 22, 107, 209, 226, 133, 13, 162, 187, 58, 81, 13, 197, 190, 41, 227, 201, 76, 169, 60, 177, 33, 113, 30})

    polyEvals[2] = make([][]frontend.Variable, 3)
    polyEvals[2][0] = utilities.ByteArrToVarArr([]uint8{36, 222, 57, 96, 229, 182, 10, 156, 146, 55, 203, 10, 82, 150, 28, 253, 37, 43, 111, 27, 253, 252, 181, 176, 186, 121, 112, 152, 120, 141, 24, 37})
    polyEvals[2][1] = utilities.ByteArrToVarArr([]uint8{12, 47, 14, 59, 235, 21, 232, 226, 218, 29, 7, 100, 248, 68, 74, 178, 117, 144, 11, 219, 204, 99, 251, 255, 12, 155, 35, 161, 100, 174, 39, 42})
    polyEvals[2][2] = utilities.ByteArrToVarArr([]uint8{71, 31, 180, 191, 83, 21, 145, 10, 45, 19, 220, 74, 19, 157, 46, 255, 166, 91, 150, 109, 181, 133, 65, 80, 227, 51, 112, 165, 48, 48, 215, 13})

    polyEvals[3] = make([][]frontend.Variable, 3)
    polyEvals[3][0] = utilities.ByteArrToVarArr([]uint8{59, 236, 36, 56, 125, 180, 76, 198, 37, 46, 34, 229, 97, 255, 170, 111, 193, 205, 54, 216, 123, 235, 177, 86, 41, 39, 98, 242, 119, 73, 50, 19})
    polyEvals[3][1] = utilities.ByteArrToVarArr([]uint8{10, 221, 44, 149, 102, 6, 104, 25, 165, 116, 244, 56, 16, 60, 17, 15, 165, 69, 119, 175, 249, 156, 36, 153, 0, 21, 38, 110, 193, 159, 173, 24})
    polyEvals[3][2] = utilities.ByteArrToVarArr([]uint8{95, 94, 210, 193, 96, 32, 213, 9, 214, 221, 89, 45, 240, 231, 183, 178, 174, 251, 51, 234, 165, 195, 177, 24, 209, 118, 90, 81, 240, 129, 246, 39})

    finalCoeffs := make([][]frontend.Variable, 1)
    finalCoeffs[0] = utilities.ByteArrToVarArr([]uint8{219, 191, 5, 3, 52, 60, 254, 232, 154, 225, 179, 221, 81, 92, 183, 236, 160, 47, 247, 170, 216, 89, 18, 10, 65, 123, 6, 176, 84, 145, 183, 24})

    nonce := utilities.ByteArrToVarArr([]uint8{0, 0, 0, 0, 0, 0, 0, 2})

    answers := [][][]frontend.Variable{
		{
            {
                utilities.NewBigIntFromString("24"),
                utilities.NewBigIntFromString("28"),
                utilities.NewBigIntFromString("32"),
                utilities.NewBigIntFromString("36"),
            },
            {
                utilities.NewBigIntFromString("18575743860132551163049618562570143701435352955997839169025642836883178712166"),
                utilities.NewBigIntFromString("7614392827869430883320186147888368183130613265973363502239242875387424482944"),
                utilities.NewBigIntFromString("18541284667445585825837159478463867753374237976364922179151047100467478749339"),
                utilities.NewBigIntFromString("7579933635182465546107727063782092235069498286340446512364647138971724520117"),
            },
            {
                utilities.NewBigIntFromString("35263367762369950740330511775103563231496777067347350277712"),
                utilities.NewBigIntFromString("35263367762369950740330511775103563231496777067347350277712"),
                utilities.NewBigIntFromString("35263367762369950740330511775103563231496777067347350277712"),
                utilities.NewBigIntFromString("35263367762369950740330511775103563231496777067347350277712"),
            },
            {
                utilities.NewBigIntFromString("3036825470211001432023850034576825283285115157561985718669349593061730636259"),
                utilities.NewBigIntFromString("13963717309787156383356665305744812538611367811729435203455348084978622472084"),
                utilities.NewBigIntFromString("3002366277524036112443074831655524705389256065480850344543142390319705812292"),
                utilities.NewBigIntFromString("13929258117100191063775890102823511960715508719648299829329140882236597648117"),
            },
            {
                utilities.NewBigIntFromString("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
                utilities.NewBigIntFromString("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
                utilities.NewBigIntFromString("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
                utilities.NewBigIntFromString("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
            },
            {
                utilities.NewBigIntFromString("3312499011706723988670051657947229906451987894211068711679007214997929228011"),
                utilities.NewBigIntFromString("14273850043969844259583642132036517739674099640459653570591212909656845887805"),
                utilities.NewBigIntFromString("3346958204393689308250826860868530484347846986292204085805214417739954051982"),
                utilities.NewBigIntFromString("14308309236656809579164417334957818317569958732540788944717420112398870711776"),
            },
            {
                utilities.NewBigIntFromString("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
                utilities.NewBigIntFromString("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
                utilities.NewBigIntFromString("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
                utilities.NewBigIntFromString("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
            },
            {
                utilities.NewBigIntFromString("18851417401628273860749291235420351285924272793061175088022408728208778414798"),
                utilities.NewBigIntFromString("7924525562052118918232317904844851715680648082669616411110604503128724148405"),
                utilities.NewBigIntFromString("18885876594315239197961750319526627233985387772694092077897004464624478377629"),
                utilities.NewBigIntFromString("7958984754739084255444776988951127663741763062302533400985200239544424111236"),
            },
        },
        {
            {
                utilities.NewBigIntFromString("6123922853079448331343150595468617552890117696294467973354470596735912462747"), 
                utilities.NewBigIntFromString("7607571759569218165742013529480170137312586498728732253382153336652725793963"), 
                utilities.NewBigIntFromString("9091220666058988000140876463491722721735055301162996533409836076569539125179"), 
                utilities.NewBigIntFromString("10574869572548757834539739397503275306157524103597260813437518816486352456395"), 
            },
            {
                utilities.NewBigIntFromString("6123922853079448331343150595468617552890117696294467973354470596735912462747"), 
                utilities.NewBigIntFromString("7607571759569218165742013529480170137312586498728732253382153336652725793963"), 
                utilities.NewBigIntFromString("9091220666058988000140876463491722721735055301162996533409836076569539125179"), 
                utilities.NewBigIntFromString("10574869572548757834539739397503275306157524103597260813437518816486352456395"), 
            },
            {
                utilities.NewBigIntFromString("6123922853079448331343150595468617552890117696294467973354470596735912462747"), 
                utilities.NewBigIntFromString("7607571759569218165742013529480170137312586498728732253382153336652725793963"), 
                utilities.NewBigIntFromString("9091220666058988000140876463491722721735055301162996533409836076569539125179"), 
                utilities.NewBigIntFromString("10574869572548757834539739397503275306157524103597260813437518816486352456395"), 
            },
            {
                utilities.NewBigIntFromString("6123922853079448331343150595468617552890117696294467973354470596735912462747"), 
                utilities.NewBigIntFromString("7607571759569218165742013529480170137312586498728732253382153336652725793963"), 
                utilities.NewBigIntFromString("9091220666058988000140876463491722721735055301162996533409836076569539125179"), 
                utilities.NewBigIntFromString("10574869572548757834539739397503275306157524103597260813437518816486352456395"),
            },
        },
	}

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
        FinalCoeffs: [][]frontend.Variable{
            make([]frontend.Variable, 32),
        },
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


