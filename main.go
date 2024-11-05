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
    ClaimedEvaluation  frontend.Variable `gnark:"Supposed evaluation for the Verifier query"`
    IOPattern []frontend.Variable `gnark:"Input output pattern for the protocol. Used to seed the initial sponge"` 
    MerkleRoots [][]frontend.Variable `gnark:"Merkle roots of the initial and folded codes"` 
    OODEvaluations [][]frontend.Variable `gnark:"Out-of-domain query evaluations"` 
	SumcheckPolysAsEvals [][][]frontend.Variable `gnark:"Quadratic sumcheck polynomials in their evaluation form (Evaluated over 0, 1, 2)"`
    FoldingParameter int
    Nonce []frontend.Variable
    Answers [][]frontend.Variable
}

func initializeSpongeWithIOPatternAndMerkleRoot (circuit *Circuit, api frontend.API) *keccakSponge.Digest {
    helperSponge, _ := keccakSponge.NewKeccak(api)
	helperSponge.Absorb(circuit.IOPattern)
	mainSponge, _ := keccakSponge.NewKeccakWithTag(api, helperSponge.Squeeze(32))
    mainSponge.Absorb(circuit.MerkleRoots[0])
    _ = typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    return mainSponge
}

func checkFirstSumcheckOfFirstRound (mainSponge *keccakSponge.Digest, circuit *Circuit, api frontend.API) {
    mainSponge.Absorb(circuit.OODEvaluations[0])
    initialCombinationRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    plugInEvaluation := api.Add(
        typeConverters.LittleEndian(api, circuit.OODEvaluations[0]), 
        api.Mul(initialCombinationRandomness, circuit.ClaimedEvaluation),
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

func initialSumcheck(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest) (foldingRandomness []frontend.Variable) {
    checkFirstSumcheckOfFirstRound(mainSponge, circuit, api)
    mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
    foldingRandomness = append(foldingRandomness, typeConverters.BigEndian(api, mainSponge.Squeeze(47)))
    for i := 1; i < circuit.FoldingParameter; i++ {
        randEval := evaluateFunction(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness[len(foldingRandomness)-1])
        checkSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
        mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
        foldingRandomness = append(foldingRandomness, typeConverters.BigEndian(api, mainSponge.Squeeze(47)))
    }
    return foldingRandomness;
}

func evaluatePolynomialFromCoeffs(api frontend.API, coefficients []frontend.Variable, point frontend.Variable) frontend.Variable {
    ans := frontend.Variable(0)
    for i := range coefficients {
        ans = api.Add(api.Mul(ans, point), coefficients[len(coefficients)-1-i])
    }
    return ans;
}

func checkRounds(api frontend.API, circuit *Circuit, mainSponge *keccakSponge.Digest, foldingRandomness []frontend.Variable) {
    mainSponge.Absorb(circuit.MerkleRoots[1])
    mainSponge.Squeeze(47)
    mainSponge.Absorb(circuit.OODEvaluations[1])
    mainSponge.Squeeze(32)
    mainSponge.Squeeze(32)
    mainSponge.Absorb(circuit.Nonce)
    combinationRandomness := typeConverters.BigEndian(api, mainSponge.Squeeze(47))
    firstPart := evaluateFunction(api, circuit.SumcheckPolysAsEvals[1], foldingRandomness[len(foldingRandomness)-1])
    values := []frontend.Variable{typeConverters.LittleEndian(api, circuit.OODEvaluations[1])}
    for i := range circuit.Answers {
        values = append(values, multivarPoly(circuit.Answers[i], foldingRandomness, api))
    }
    secondPart := evaluatePolynomialFromCoeffs(api, values, combinationRandomness)
    val := api.Add(firstPart, secondPart)
    checkSumOverBool(api, val, circuit.SumcheckPolysAsEvals[2])
}

func (circuit *Circuit) Define(api frontend.API) error {
    mainSponge := initializeSpongeWithIOPatternAndMerkleRoot(circuit, api)
    foldingRandomness := initialSumcheck(api, circuit, mainSponge)
    checkRounds(api, circuit, mainSponge, foldingRandomness)
    return nil
}

func newBigInt(s string) *big.Int {
    bigInt, _ := new(big.Int).SetString(s, 10)
    return bigInt
}

func multivarPoly (coefs []frontend.Variable, vars []frontend.Variable, api frontend.API) frontend.Variable {
	if (len(vars) == 0) { return coefs[0] }
	deg_zero := multivarPoly(coefs[:len(coefs)/2], vars[:len(vars)-1], api)
	deg_one := api.Mul(vars[len(vars)-1], multivarPoly(coefs[len(coefs)/2:], vars[:len(vars)-1], api))
	return api.Add(deg_zero, deg_one)
}

func main() {
    claimedEvaluation, _ := new(big.Int).SetString("120", 10)
    iopattern := typeConverters.ByteArrToVarArr([]uint8{240, 159, 140, 170, 239, 184, 143, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 52, 55, 105, 110, 105, 116, 105, 97, 108, 95, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 109, 101, 114, 107, 108, 101, 95, 100, 105, 103, 101, 115, 116, 0, 83, 52, 55, 111, 111, 100, 95, 113, 117, 101, 114, 121, 0, 65, 51, 50, 111, 111, 100, 95, 97, 110, 115, 0, 83, 51, 50, 115, 116, 105, 114, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101, 0, 83, 52, 55, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 57, 54, 115, 117, 109, 99, 104, 101, 99, 107, 95, 112, 111, 108, 121, 0, 83, 52, 55, 102, 111, 108, 100, 105, 110, 103, 95, 114, 97, 110, 100, 111, 109, 110, 101, 115, 115, 0, 65, 51, 50, 102, 105, 110, 97, 108, 95, 99, 111, 101, 102, 102, 115, 0, 83, 51, 50, 102, 105, 110, 97, 108, 95, 113, 117, 101, 114, 105, 101, 115, 95, 115, 101, 101, 100, 0, 83, 51, 50, 112, 111, 119, 95, 113, 117, 101, 114, 105, 101, 115, 0, 65, 56, 112, 111, 119, 45, 110, 111, 110, 99, 101})
    merkleRoots := [][]frontend.Variable{
        typeConverters.ByteArrToVarArr([]uint8{86, 75, 127, 228, 31, 170, 126, 19, 179, 209, 30, 107, 197, 173, 186, 0, 131, 133, 127, 240, 217, 73, 50, 206, 238, 236, 139, 69, 35, 155, 79, 52}),
        typeConverters.ByteArrToVarArr([]uint8{58, 107, 66, 235, 56, 51, 242, 113, 19, 161, 88, 169, 3, 19, 148, 198, 203, 99, 180, 237, 215, 227, 237, 177, 254, 215, 105, 94, 32, 218, 14, 48}),
    }
    oodEvaluations := [][]frontend.Variable{
        typeConverters.ByteArrToVarArr([]uint8{34, 222, 231, 144, 26, 1, 111, 94, 211, 208, 9, 123, 2, 128, 115, 36, 22, 167, 134, 143, 221, 216, 151, 218, 157, 62, 24, 220, 237, 200, 176, 1}),
        typeConverters.ByteArrToVarArr([]uint8{213, 6, 31, 254, 249, 36, 42, 55, 223, 187, 1, 200, 255, 121, 213, 241, 184, 70, 177, 234, 131, 195, 16, 25, 49, 76, 127, 234, 41, 200, 173, 33}),
    }
    polyEvals := make([][][]frontend.Variable, 3)
    
    polyEvals[0] = make([][]frontend.Variable, 3)
    polyEvals[0][0] = typeConverters.ByteArrToVarArr([]uint8{10, 143, 212, 116, 96, 10, 226, 127, 95, 1, 246, 48, 167, 203, 62, 162, 81, 180, 163, 21, 86, 15, 90, 210, 104, 41, 43, 65, 57, 97, 216, 2})
    polyEvals[0][1] = typeConverters.ByteArrToVarArr([]uint8{16, 231, 231, 70, 86, 121, 22, 112, 238, 188, 214, 38, 191, 177, 218, 217, 15, 87, 199, 194, 137, 196, 39, 204, 50, 144, 170, 76, 4, 153, 217, 34})
    polyEvals[0][2] = typeConverters.ByteArrToVarArr([]uint8{178, 27, 127, 170, 216, 180, 22, 55, 14, 6, 94, 105, 187, 199, 27, 167, 68, 211, 132, 158, 3, 200, 53, 1, 134, 230, 255, 21, 71, 71, 70, 9})
    
    polyEvals[1] = make([][]frontend.Variable, 3)
    polyEvals[1][0] = typeConverters.ByteArrToVarArr([]uint8{220, 96, 19, 56, 152, 181, 63, 207, 103, 60, 8, 100, 22, 1, 165, 98, 58, 118, 96, 154, 94, 6, 165, 169, 236, 169, 193, 213, 102, 44, 138, 37})
    polyEvals[1][1] = typeConverters.ByteArrToVarArr([]uint8{42, 18, 253, 161, 116, 205, 150, 65, 85, 51, 244, 44, 181, 126, 51, 166, 64, 126, 159, 24, 100, 48, 60, 148, 63, 110, 25, 189, 178, 25, 46, 10})
    polyEvals[1][2] = typeConverters.ByteArrToVarArr([]uint8{239, 220, 57, 83, 59, 170, 35, 30, 164, 22, 107, 209, 226, 133, 13, 162, 187, 58, 81, 13, 197, 190, 41, 227, 201, 76, 169, 60, 177, 33, 113, 30})

    polyEvals[2] = make([][]frontend.Variable, 3)
    polyEvals[2][0] = typeConverters.ByteArrToVarArr([]uint8{36, 222, 57, 96, 229, 182, 10, 156, 146, 55, 203, 10, 82, 150, 28, 253, 37, 43, 111, 27, 253, 252, 181, 176, 186, 121, 112, 152, 120, 141, 24, 37})
    polyEvals[2][1] = typeConverters.ByteArrToVarArr([]uint8{12, 47, 14, 59, 235, 21, 232, 226, 218, 29, 7, 100, 248, 68, 74, 178, 117, 144, 11, 219, 204, 99, 251, 255, 12, 155, 35, 161, 100, 174, 39, 42})
    polyEvals[2][2] = typeConverters.ByteArrToVarArr([]uint8{71, 31, 180, 191, 83, 21, 145, 10, 45, 19, 220, 74, 19, 157, 46, 255, 166, 91, 150, 109, 181, 133, 65, 80, 227, 51, 112, 165, 48, 48, 215, 13})

    nonce := typeConverters.ByteArrToVarArr([]uint8{0, 0, 0, 0, 0, 0, 0, 2})

    answers := [][]frontend.Variable{
		{
			newBigInt("24"),
			newBigInt("28"),
			newBigInt("32"),
			newBigInt("36"),
		},
		{
			newBigInt("18575743860132551163049618562570143701435352955997839169025642836883178712166"),
			newBigInt("7614392827869430883320186147888368183130613265973363502239242875387424482944"),
			newBigInt("18541284667445585825837159478463867753374237976364922179151047100467478749339"),
			newBigInt("7579933635182465546107727063782092235069498286340446512364647138971724520117"),
		},
		{
			newBigInt("35263367762369950740330511775103563231496777067347350277712"),
			newBigInt("35263367762369950740330511775103563231496777067347350277712"),
			newBigInt("35263367762369950740330511775103563231496777067347350277712"),
			newBigInt("35263367762369950740330511775103563231496777067347350277712"),
		},
		{
			newBigInt("3036825470211001432023850034576825283285115157561985718669349593061730636259"),
			newBigInt("13963717309787156383356665305744812538611367811729435203455348084978622472084"),
			newBigInt("3002366277524036112443074831655524705389256065480850344543142390319705812292"),
			newBigInt("13929258117100191063775890102823511960715508719648299829329140882236597648117"),
		},
		{
			newBigInt("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
			newBigInt("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
			newBigInt("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
			newBigInt("21888242871839275222246405745257275088548364400416034343698204186575808495609"),
		},
		{
			newBigInt("3312499011706723988670051657947229906451987894211068711679007214997929228011"),
			newBigInt("14273850043969844259583642132036517739674099640459653570591212909656845887805"),
			newBigInt("3346958204393689308250826860868530484347846986292204085805214417739954051982"),
			newBigInt("14308309236656809579164417334957818317569958732540788944717420112398870711776"),
		},
		{
			newBigInt("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
			newBigInt("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
			newBigInt("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
			newBigInt("21888242871839275186983037982887324348217852625312471112201427119228458217889"),
		},
		{
			newBigInt("18851417401628273860749291235420351285924272793061175088022408728208778414798"),
			newBigInt("7924525562052118918232317904844851715680648082669616411110604503128724148405"),
			newBigInt("18885876594315239197961750319526627233985387772694092077897004464624478377629"),
			newBigInt("7958984754739084255444776988951127663741763062302533400985200239544424111236"),
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
        },
        FoldingParameter: 2,
        Nonce: make([]frontend.Variable, len(nonce)),
        Answers: [][]frontend.Variable{
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
            make([]frontend.Variable, 4),
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
    }

    witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
    publicWitness, _ := witness.Public()
    proof, _ := groth16.Prove(ccs, pk, witness)
    groth16.Verify(proof, vk, publicWitness)
}


