package main

import (
	"math/big"
	"math/bits"
	"reilabs/whir-verifier-circuit/typeConverters"
	"reilabs/whir-verifier-circuit/utilities"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/math/uints"
	gnark_nimue "github.com/reilabs/gnark-nimue"
	skyscraper "github.com/reilabs/gnark-skyscraper"
)

type Circuit struct {
	// Inputs
	DomainSize                           int
	StartingDomainBackingDomainGenerator frontend.Variable
	CommittmentOODSamples                int
	FoldingFactor                        int
	FinalSumcheckRounds                  int
	ParamNRounds                         int
	MVParamsNumberOfVariables            int
	RoundParametersOODSamples            []int
	RoundParametersNumOfQueries          []int
	InitialStatement                     bool
	FoldOptimisation                     bool
	PowBits                              []int
	FinalPowBits                         int
	FinalFoldingPowBits                  int
	FinalQueries                         int
	Leaves                               [][][]frontend.Variable
	LeafIndexes                          [][]uints.U64
	LeafSiblingHashes                    [][][]uints.U8
	AuthPaths                            [][][][]uints.U8
	StatementPoints                      [][]frontend.Variable
	StatementEvaluations                 int
	LinearStatementValuesAtPoints        []frontend.Variable
	LinearStatementEvaluations           []frontend.Variable
	NVars                                int
	// Public Input
	IO         []byte
	Transcript []uints.U8 `gnark:",public"`
}

func GetStirChallenges(
	api frontend.API,
	circuit Circuit,
	arthur gnark_nimue.Arthur,
	numQueries int,
	domainSize int,
) ([]frontend.Variable, error) {
	foldedDomainSize := domainSize / (1 << circuit.FoldingFactor)
	domainSizeBytes := (bits.Len(uint(foldedDomainSize*2-1)) - 1 + 7) / 8

	stirQueries := make([]uints.U8, domainSizeBytes*numQueries)
	if err := arthur.FillChallengeBytes(stirQueries); err != nil {
		return nil, err
	}

	bitLength := bits.Len(uint(foldedDomainSize)) - 1

	indexes := make([]frontend.Variable, numQueries)
	for i := range numQueries {
		var value frontend.Variable = 0
		for j := range domainSizeBytes {
			value = api.Add(stirQueries[j+i*domainSizeBytes].Val, api.Mul(value, 256))
		}

		bitsOfValue := api.ToBinary(value)
		indexes[i] = api.FromBinary(bitsOfValue[:bitLength]...)
	}

	return indexes, nil
}

func VerifyMerkleTreeProofs(api frontend.API, uapi *uints.BinaryField[uints.U64], sc *skyscraper.Skyscraper, leafIndexes []uints.U64, leaves [][]frontend.Variable, leafSiblingHashes [][]uints.U8, authPaths [][][]uints.U8, rootHash frontend.Variable) error {
	numOfLeavesProved := len(leaves)
	for i := range numOfLeavesProved {
		treeHeight := len(authPaths[i]) + 1
		leafIndexBits := api.ToBinary(uapi.ToValue(leafIndexes[i]), treeHeight)
		leafSiblingHash := typeConverters.LittleEndianFromUints(api, leafSiblingHashes[i])

		claimedLeafHash := sc.Compress(leaves[i][0], leaves[i][1])
		for x := range len(leaves[i]) - 2 {
			claimedLeafHash = sc.Compress(claimedLeafHash, leaves[i][x+2])
		}

		dir := leafIndexBits[0]

		x_leftChild := api.Select(dir, leafSiblingHash, claimedLeafHash)
		x_rightChild := api.Select(dir, claimedLeafHash, leafSiblingHash)

		currentHash := sc.Compress(x_leftChild, x_rightChild)

		for level := 1; level < treeHeight; level++ {
			indexBit := leafIndexBits[level]

			siblingHash := typeConverters.LittleEndianFromUints(api, authPaths[i][level-1])

			dir := api.And(indexBit, 1)
			left := api.Select(dir, siblingHash, currentHash)
			right := api.Select(dir, currentHash, siblingHash)

			currentHash = sc.Compress(left, right)
		}
		api.AssertIsEqual(currentHash, rootHash)
	}
	return nil
}

func checkTheVeryFirstSumcheck(api frontend.API, circuit *Circuit, firstOODAnswers []frontend.Variable, initialCombinationRandomness []frontend.Variable, sumcheckRounds [][][]frontend.Variable) {
	plugInEvaluation := frontend.Variable(0)
	for i := range initialCombinationRandomness {
		if i < len(firstOODAnswers) {
			plugInEvaluation = api.Add(
				plugInEvaluation,
				api.Mul(initialCombinationRandomness[i], firstOODAnswers[i]),
			)
		} else {
			plugInEvaluation = api.Add(
				plugInEvaluation,
				api.Mul(initialCombinationRandomness[i], circuit.LinearStatementEvaluations[i-len(firstOODAnswers)]),
			)
		}
	}
	utilities.CheckSumOverBool(api, plugInEvaluation, sumcheckRounds[0][0])
}

func initialSumcheck(
	api frontend.API,
	circuit *Circuit,
	firstOODAnswers []frontend.Variable,
	initialCombinationRandomness []frontend.Variable,
	sumcheckRounds [][][]frontend.Variable,
) {

	checkTheVeryFirstSumcheck(api, circuit, firstOODAnswers, initialCombinationRandomness, sumcheckRounds)

	for roundIndex := 1; roundIndex < circuit.FoldingFactor; roundIndex++ {
		evaluatedPolyAtRandomness := utilities.EvaluateQuadraticPolynomialFromEvaluationList(
			api,
			sumcheckRounds[roundIndex-1][0],
			sumcheckRounds[roundIndex-1][1][0],
		)

		utilities.CheckSumOverBool(api, evaluatedPolyAtRandomness, sumcheckRounds[roundIndex][0])
	}
}

func checkMainRounds(
	api frontend.API,
	circuit *Circuit,
	sumcheckRounds [][][]frontend.Variable,
	sumcheckPolynomials [][][]frontend.Variable,
	finalFoldingRandomness [][]frontend.Variable,
	oodPointsList [][]frontend.Variable,
	oodAnswersList [][]frontend.Variable,
	combinationRandomness [][]frontend.Variable,
	finalCoefficients []frontend.Variable,
	finalRandomnessPoints []frontend.Variable,
	initialOODQueries []frontend.Variable,
	initialCombinationRandomness []frontend.Variable,
	stirChallengesPoints [][]frontend.Variable,
	perRoundCombinationRandomness [][]frontend.Variable,
	finalSumcheckRandomness []frontend.Variable,
	finalSumcheckRounds [][][]frontend.Variable,
) {
	computedFolds := ComputeFolds(api, circuit, sumcheckRounds, finalFoldingRandomness)

	var lastEval frontend.Variable
	prevPoly := sumcheckRounds[len(sumcheckRounds)-1][0][:]
	prevRandomness := sumcheckRounds[len(sumcheckRounds)-1][1][0]

	for roundIndex := range circuit.RoundParametersOODSamples {
		currentValues := make([]frontend.Variable, len(computedFolds[roundIndex])+1)
		currentValues[0] = oodAnswersList[roundIndex][0]
		copy(currentValues[1:], computedFolds[roundIndex][:])

		valuesTimesCombRand := frontend.Variable(0)
		for i, val := range currentValues {
			product := api.Mul(val, combinationRandomness[roundIndex][i])
			valuesTimesCombRand = api.Add(valuesTimesCombRand, product)
		}
		claimedSum := api.Add(utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, prevPoly, prevRandomness), valuesTimesCombRand)

		utilities.CheckSumOverBool(api, claimedSum, sumcheckPolynomials[roundIndex][0])

		prevPoly = sumcheckPolynomials[roundIndex][0][:]
		for polyIndex := 1; polyIndex < len(sumcheckPolynomials[roundIndex]); polyIndex++ {
			eval := utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, sumcheckPolynomials[roundIndex][polyIndex-1], finalFoldingRandomness[roundIndex][polyIndex-1])
			lastEval = eval

			utilities.CheckSumOverBool(api, eval, sumcheckPolynomials[roundIndex][polyIndex])

			prevPoly = sumcheckPolynomials[roundIndex][polyIndex]
			prevRandomness = finalFoldingRandomness[roundIndex][polyIndex]
		}

		lastEval = utilities.EvaluateQuadraticPolynomialFromEvaluationList(
			api,
			sumcheckPolynomials[roundIndex][len(sumcheckPolynomials[roundIndex])-1],
			finalFoldingRandomness[roundIndex][len(sumcheckPolynomials[roundIndex])-1],
		)
	}

	finalEvaluations := utilities.UnivarPoly(api, finalCoefficients, finalRandomnessPoints)

	finalFolds := computedFolds[len(computedFolds)-1]
	for foldIndex := range finalFolds {
		api.AssertIsEqual(finalFolds[foldIndex], finalEvaluations[foldIndex])
	}

	if circuit.FinalSumcheckRounds > 0 {
		utilities.CheckSumOverBool(api, lastEval, finalSumcheckRounds[0][0])

		for round := 1; round < len(finalSumcheckRounds); round++ {
			eval := utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, finalSumcheckRounds[round-1][0], finalSumcheckRounds[round-1][1][0])
			lastEval = eval
			utilities.CheckSumOverBool(api, eval, finalSumcheckRounds[round][0])
		}

		lastEval = utilities.EvaluateQuadraticPolynomialFromEvaluationList(
			api,
			finalSumcheckRounds[len(finalSumcheckRounds)-1][0],
			finalSumcheckRounds[len(finalSumcheckRounds)-1][1][0],
		)
	}

	evaluationOfVPoly := ComputeVPoly(
		api,
		circuit,
		finalFoldingRandomness,
		sumcheckRounds,
		initialOODQueries,
		circuit.StatementPoints,
		initialCombinationRandomness,
		oodPointsList,
		stirChallengesPoints,
		perRoundCombinationRandomness,
		finalSumcheckRandomness,
	)
	api.AssertIsEqual(
		lastEval,
		api.Mul(evaluationOfVPoly, utilities.MultivarPoly(finalCoefficients, finalSumcheckRandomness, api)),
	)
}

func ComputeVPoly(api frontend.API, circuit *Circuit, finalFoldingRandomness [][]frontend.Variable, sumcheckRounds [][][]frontend.Variable, initialOODQueries []frontend.Variable, statementPoints [][]frontend.Variable, initialCombinationRandomness []frontend.Variable, oodPointLists [][]frontend.Variable, stirChallengesPoints [][]frontend.Variable, perRoundCombinationRandomness [][]frontend.Variable, finalSumcheckRandomness []frontend.Variable) frontend.Variable {
	foldingRandomness := make([]frontend.Variable, len(finalFoldingRandomness[0])*len(finalFoldingRandomness)+len(sumcheckRounds)+len(finalSumcheckRandomness))
	for j := range len(finalSumcheckRandomness) {
		foldingRandomness[j] = finalSumcheckRandomness[len(finalSumcheckRandomness)-1-j]
	}
	ind := len(finalSumcheckRandomness)
	for j := range len(finalFoldingRandomness) {
		for i := range len(finalFoldingRandomness[j]) {
			foldingRandomness[ind] = finalFoldingRandomness[len(finalFoldingRandomness)-1-j][len(finalFoldingRandomness[j])-1-i]
			ind = ind + 1
		}
	}
	for j := range len(sumcheckRounds) {
		foldingRandomness[ind] = sumcheckRounds[len(sumcheckRounds)-1-j][1][0]
		ind = ind + 1
	}

	numVariables := circuit.MVParamsNumberOfVariables

	value := frontend.Variable(0)
	for j := range initialOODQueries {
		value = api.Add(value, api.Mul(initialCombinationRandomness[j], utilities.EqPolyOutside(api, utilities.ExpandFromUnivariate(api, initialOODQueries[j], numVariables), foldingRandomness)))
	}
	for j := range circuit.LinearStatementValuesAtPoints {
		value = api.Add(value, api.Mul(initialCombinationRandomness[len(initialOODQueries)+j], circuit.LinearStatementValuesAtPoints[j]))
	}

	numberVars := numVariables

	for r := range oodPointLists {
		newTmpArr := make([]frontend.Variable, len(oodPointLists[r])+len(stirChallengesPoints[r]))
		numberVars -= circuit.FoldingFactor
		for i := range oodPointLists[r] {
			newTmpArr[i] = oodPointLists[r][i]
		}
		for i := range stirChallengesPoints[r] {
			newTmpArr[i+len(oodPointLists[r])] = stirChallengesPoints[r][i]
		}
		revTmpArr := make([]frontend.Variable, len(oodPointLists[r])+len(stirChallengesPoints[r]))

		for i := range len(oodPointLists[r]) + len(stirChallengesPoints[r]) {
			revTmpArr[i] = newTmpArr[len(oodPointLists[r])+len(stirChallengesPoints[r])-1-i]
		}
		sumOfClaims := frontend.Variable(0)
		for i := range newTmpArr {
			point := utilities.ExpandFromUnivariate(api, newTmpArr[i], numberVars)
			sumOfClaims = api.Add(sumOfClaims, api.Mul(utilities.EqPolyOutside(api, point, foldingRandomness[0:numberVars]), perRoundCombinationRandomness[r][i]))
		}
		value = api.Add(value, sumOfClaims)
	}

	return value
}

func ComputeFoldsHelped(api frontend.API, circuit *Circuit, sumcheckRounds [][][]frontend.Variable, finalFoldingRandomness [][]frontend.Variable) [][]frontend.Variable {
	result := make([][]frontend.Variable, len(circuit.Leaves))

	for i := range len(circuit.Leaves) - 1 {
		evaluations := make([]frontend.Variable, len(circuit.Leaves[i]))
		for j := range circuit.Leaves[i] {
			lenAns := len(circuit.Leaves[i][j])
			answerList := make([]frontend.Variable, lenAns)
			for z := range lenAns {
				answerList[z] = circuit.Leaves[i][j][z]
			}
			reverseRounds := make([]frontend.Variable, len(sumcheckRounds))
			if i == 0 {
				for z := range len(sumcheckRounds) {
					reverseRounds[z] = sumcheckRounds[z][1][0]
				}
			} else {
				for z := range len(finalFoldingRandomness[i-1]) {
					reverseRounds[z] = finalFoldingRandomness[i-1][z]
				}
			}
			evaluations[j] = utilities.MultivarPoly(answerList, reverseRounds, api)
		}
		result[i] = evaluations
	}

	evaluations := make([]frontend.Variable, len(circuit.Leaves[len(circuit.Leaves)-1]))
	for j := range circuit.Leaves[len(circuit.Leaves)-1] {
		answListLen := len(circuit.Leaves[len(circuit.Leaves)-1][j])
		answerList := make([]frontend.Variable, answListLen)
		for z := range answListLen {
			answerList[z] = circuit.Leaves[len(circuit.Leaves)-1][j][z]
		}
		evaluations[j] = utilities.MultivarPoly(answerList, finalFoldingRandomness[len(finalFoldingRandomness)-1], api)
	}
	result[len(result)-1] = evaluations
	return result
}

func ComputeFoldsFull(api frontend.API, circuit *Circuit) [][]frontend.Variable {
	return nil
}

func ComputeFolds(api frontend.API, circuit *Circuit, sumcheckRounds [][][]frontend.Variable, finalFoldingRandomness [][]frontend.Variable) [][]frontend.Variable {
	if circuit.FoldOptimisation {
		return ComputeFoldsHelped(api, circuit, sumcheckRounds, finalFoldingRandomness)
	} else {
		return ComputeFoldsFull(api, circuit)
	}
}

func calculateEQ(api frontend.API, alphas []frontend.Variable, r []frontend.Variable) frontend.Variable {
	ans := frontend.Variable(1)
	for i, alpha := range alphas {
		ans = api.Mul(ans, api.Add(api.Mul(alpha, r[i]), api.Mul(api.Sub(frontend.Variable(1), alpha), api.Sub(frontend.Variable(1), r[i]))))
	}
	return ans
}

func (circuit *Circuit) Define(api frontend.API) error {
	sc := skyscraper.NewSkyscraper(api, 2)
	arthur, err := gnark_nimue.NewSkyscraperArthur(api, sc, circuit.IO, circuit.Transcript[:])
	if err != nil {
		return err
	}

	uapi, err := uints.New[uints.U64](api)
	if err != nil {
		return err
	}

	// TODO: remove this after Spartan verifier is done
	t_rand := make([]frontend.Variable, circuit.NVars)
	if err = arthur.FillChallengeScalars(t_rand); err != nil {
		return err
	}

	savedValForSumcheck := frontend.Variable(0)

	sp_rand := make([]frontend.Variable, circuit.NVars)
	sp_rand_temp := make([]frontend.Variable, 1)
	for i := 0; i < circuit.NVars; i++ {
		sp := make([]frontend.Variable, 4)
		if err = arthur.FillNextScalars(sp); err != nil {
			return err
		}
		if err = arthur.FillChallengeScalars(sp_rand_temp); err != nil {
			return err
		}
		sp_rand[i] = sp_rand_temp[0]
		sumcheckVal := api.Add(utilities.UnivarPoly(api, sp, []frontend.Variable{0})[0], utilities.UnivarPoly(api, sp, []frontend.Variable{1})[0])
		api.AssertIsEqual(sumcheckVal, savedValForSumcheck)
		savedValForSumcheck = utilities.UnivarPoly(api, sp, []frontend.Variable{sp_rand[i]})[0]
	}

	finalFoldingRandomness := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	sumcheckPolynomials := make([][][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	oodPointsList := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	oodAnswersList := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	perRoundCombinationRandomness := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	exp := uint64(1 << circuit.FoldingFactor)
	expDomainGenerator := utilities.Exponent(api, uapi, circuit.StartingDomainBackingDomainGenerator, uints.NewU64(exp))
	domainSize := circuit.DomainSize

	rootHash := make([]frontend.Variable, 1)
	if err = arthur.FillNextScalars(rootHash); err != nil {
		return err
	}

	initialOODQueries := make([]frontend.Variable, circuit.CommittmentOODSamples)
	if err = arthur.FillChallengeScalars(initialOODQueries); err != nil {
		return err
	}

	initialOODAnswers := make([]frontend.Variable, circuit.CommittmentOODSamples)
	if err = arthur.FillNextScalars(initialOODAnswers); err != nil {
		return err
	}

	// if circuit.InitialStatement {
	combinationRandomnessGenerator := make([]frontend.Variable, 1)
	if err = arthur.FillChallengeScalars(combinationRandomnessGenerator); err != nil {
		return err
	}

	initialCombinationRandomness := utilities.ExpandRandomness(api, combinationRandomnessGenerator[0], circuit.CommittmentOODSamples+len(circuit.LinearStatementEvaluations))

	sumcheckRounds := make([][][]frontend.Variable, circuit.FoldingFactor)
	for i := range circuit.FoldingFactor {
		sumcheckRounds[i] = make([][]frontend.Variable, 2)
		sumcheckPolynomialEvals := make([]frontend.Variable, 3)

		if err = arthur.FillNextScalars(sumcheckPolynomialEvals); err != nil {
			return err
		}

		foldingRandomnessSingle := make([]frontend.Variable, 1)
		if err = arthur.FillChallengeScalars(foldingRandomnessSingle); err != nil {
			return err
		}

		sumcheckRounds[i][0] = sumcheckPolynomialEvals
		sumcheckRounds[i][1] = foldingRandomnessSingle
	}
	initialSumcheck(api, circuit, initialOODAnswers, initialCombinationRandomness, sumcheckRounds)
	// // } else {
	// // 	initialCombinationRandomness = []frontend.Variable{1}
	// // }

	roots := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	stirChallengesPoints := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	prevRoot := rootHash[0]
	for r := range circuit.RoundParametersOODSamples {
		roots[r] = make([]frontend.Variable, 1)
		if err = arthur.FillNextScalars(roots[r]); err != nil {
			return err
		}

		err = VerifyMerkleTreeProofs(api, uapi, sc, circuit.LeafIndexes[r], circuit.Leaves[r], circuit.LeafSiblingHashes[r], circuit.AuthPaths[r], prevRoot)
		if err != nil {
			return err
		}

		prevRoot = roots[r][0]
		oodPoints := make([]frontend.Variable, circuit.RoundParametersOODSamples[r])
		oodAnswers := make([]frontend.Variable, circuit.RoundParametersOODSamples[r])

		if circuit.RoundParametersOODSamples[r] > 0 {
			if err = arthur.FillChallengeScalars(oodPoints); err != nil {
				return err
			}

			if err = arthur.FillNextScalars(oodAnswers); err != nil {
				return err
			}

			oodPointsList[r] = oodPoints
			oodAnswersList[r] = oodAnswers
		}

		indexes, err := GetStirChallenges(api, *circuit, arthur, circuit.RoundParametersNumOfQueries[r], domainSize)
		if err != nil {
			return err
		}

		err = utilities.IsSubset(api, uapi, arthur, indexes, circuit.LeafIndexes[r])
		if err != nil {
			return err
		}
		stirChallengesPoints[r] = make([]frontend.Variable, len(circuit.LeafIndexes[r]))

		for index := range circuit.LeafIndexes[r] {
			x := utilities.Exponent(api, uapi, expDomainGenerator, circuit.LeafIndexes[r][index])
			stirChallengesPoints[r][index] = x
		}
		// api.Println(circuit.PowBytes)
		if circuit.PowBits[r] > 0 {
			_, _, err := utilities.PoW(api, sc, arthur, circuit.PowBits[r])
			if err != nil {
				return err
			}
			// api.Println(challenge)
			// api.Println(nonce)
		}

		combRandomnessGen := make([]frontend.Variable, 1)
		if err = arthur.FillChallengeScalars(combRandomnessGen); err != nil {
			return err
		}

		combinationRandomness := utilities.ExpandRandomness(api, combRandomnessGen[0], len(circuit.LeafIndexes[r])+circuit.RoundParametersOODSamples[r])
		perRoundCombinationRandomness[r] = combinationRandomness

		finalFoldingRandomness[r] = make([]frontend.Variable, circuit.FoldingFactor)
		sumcheckPolynomials[r] = make([][]frontend.Variable, circuit.FoldingFactor)

		for i := range circuit.FoldingFactor {
			sumcheckPoly := make([]frontend.Variable, 3)
			if err = arthur.FillNextScalars(sumcheckPoly); err != nil {
				return err
			}

			sumcheckPolynomials[r][i] = sumcheckPoly

			foldingRandomnessSingle := make([]frontend.Variable, 1)
			if err = arthur.FillChallengeScalars(foldingRandomnessSingle); err != nil {
				return err
			}
			finalFoldingRandomness[r][i] = foldingRandomnessSingle[0]
		}

		domainSize /= 2
		expDomainGenerator = api.Mul(expDomainGenerator, expDomainGenerator)
	}
	finalCoefficients := make([]frontend.Variable, 1<<circuit.FinalSumcheckRounds)
	if err = arthur.FillNextScalars(finalCoefficients); err != nil {
		return err
	}

	finalIndexes, err := GetStirChallenges(api, *circuit, arthur, circuit.FinalQueries, domainSize)
	if err != nil {
		api.Println(err)
		return nil
	}

	err = utilities.IsSubset(api, uapi, arthur, finalIndexes, circuit.LeafIndexes[len(circuit.LeafIndexes)-1])
	if err != nil {
		return err
	}

	finalRandomnessPoints := make([]frontend.Variable, len(circuit.LeafIndexes[len(circuit.LeafIndexes)-1]))

	for index := range circuit.LeafIndexes[len(circuit.LeafIndexes)-1] {
		finalRandomnessPoints[index] = utilities.Exponent(api, uapi, expDomainGenerator, circuit.LeafIndexes[len(circuit.LeafIndexes)-1][index])
	}

	err = VerifyMerkleTreeProofs(api, uapi, sc, circuit.LeafIndexes[len(circuit.LeafIndexes)-1], circuit.Leaves[len(circuit.LeafIndexes)-1], circuit.LeafSiblingHashes[len(circuit.LeafIndexes)-1], circuit.AuthPaths[len(circuit.LeafIndexes)-1], prevRoot)
	if err != nil {
		return err
	}

	if circuit.FinalPowBits > 0 {
		_, _, err := utilities.PoW(api, sc, arthur, circuit.FinalPowBits)
		if err != nil {
			return err
		}
		// api.Println(finalChallenge)
		// api.Println(finalNonce)
	}

	finalSumcheckRounds := make([][][]frontend.Variable, circuit.FinalSumcheckRounds)
	finalSumcheckRandomness := make([]frontend.Variable, circuit.FinalSumcheckRounds)

	for i := range circuit.FinalSumcheckRounds {
		finalSumcheckPolyEvals := make([]frontend.Variable, 3)
		if err = arthur.FillNextScalars(finalSumcheckPolyEvals); err != nil {
			return err
		}

		finalFoldingRandomnessSingle := make([]frontend.Variable, 1)
		if err = arthur.FillChallengeScalars(finalFoldingRandomnessSingle); err != nil {
			return err
		}

		finalSumcheckRounds[i] = make([][]frontend.Variable, 2)
		finalSumcheckRounds[i][0] = finalSumcheckPolyEvals
		finalSumcheckRounds[i][1] = finalFoldingRandomnessSingle
		finalSumcheckRandomness[i] = finalFoldingRandomnessSingle[0]
		if circuit.FinalFoldingPowBits > 0 {
			utilities.PoW(api, sc, arthur, circuit.FinalFoldingPowBits)
		}
	}

	checkMainRounds(api, circuit, sumcheckRounds, sumcheckPolynomials, finalFoldingRandomness, oodPointsList, oodAnswersList, perRoundCombinationRandomness, finalCoefficients, finalRandomnessPoints, initialOODQueries, initialCombinationRandomness, stirChallengesPoints, perRoundCombinationRandomness, finalSumcheckRandomness, finalSumcheckRounds)

	x := api.Mul(api.Sub(api.Mul(circuit.LinearStatementEvaluations[0], circuit.LinearStatementEvaluations[1]), circuit.LinearStatementEvaluations[2]), calculateEQ(api, sp_rand, t_rand))

	api.AssertIsEqual(savedValForSumcheck, x)
	return nil
}

func verify_circuit(proof_arg ProofObject, cfg Config) {
	proofs := proof_arg.MerklePaths
	var totalAuthPath = make([][][][]uints.U8, len(proofs))
	var totalLeaves = make([][][]frontend.Variable, len(proofs))
	var totalLeafSiblingHashes = make([][][]uints.U8, len(proofs))
	var totalLeafIndexes = make([][]uints.U64, len(proofs))

	var containerTotalAuthPath = make([][][][]uints.U8, len(proofs))
	var containerTotalLeaves = make([][][]frontend.Variable, len(proofs))
	var containerTotalLeafSiblingHashes = make([][][]uints.U8, len(proofs))
	var containerTotalLeafIndexes = make([][]uints.U64, len(proofs))

	for i := range proofs {
		var numOfLeavesProved = len(proofs[i].A.LeafIndexes)
		var treeHeight = len(proofs[i].A.AuthPathsSuffixes[0])

		totalAuthPath[i] = make([][][]uints.U8, numOfLeavesProved)
		containerTotalAuthPath[i] = make([][][]uints.U8, numOfLeavesProved)
		totalLeaves[i] = make([][]frontend.Variable, numOfLeavesProved)
		containerTotalLeaves[i] = make([][]frontend.Variable, numOfLeavesProved)
		totalLeafSiblingHashes[i] = make([][]uints.U8, numOfLeavesProved)
		containerTotalLeafSiblingHashes[i] = make([][]uints.U8, numOfLeavesProved)

		for j := range numOfLeavesProved {
			totalAuthPath[i][j] = make([][]uints.U8, treeHeight)
			containerTotalAuthPath[i][j] = make([][]uints.U8, treeHeight)

			for z := range treeHeight {
				totalAuthPath[i][j][z] = make([]uints.U8, 32)
				containerTotalAuthPath[i][j][z] = make([]uints.U8, 32)
			}
			totalLeaves[i][j] = make([]frontend.Variable, len(proofs[i].B[j]))
			containerTotalLeaves[i][j] = make([]frontend.Variable, len(proofs[i].B[j]))
			totalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
			containerTotalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
		}

		containerTotalLeafIndexes[i] = make([]uints.U64, numOfLeavesProved)

		var authPathsTemp = make([][]KeccakDigest, numOfLeavesProved)
		var prevPath = proofs[i].A.AuthPathsSuffixes[0]
		authPathsTemp[0] = utilities.Reverse(prevPath)

		for j := range totalAuthPath[i][0] {
			totalAuthPath[i][0][j] = uints.NewU8Array(authPathsTemp[0][j].KeccakDigest[:])
		}

		for j := 1; j < numOfLeavesProved; j++ {
			prevPath = utilities.PrefixDecodePath(prevPath, proofs[i].A.AuthPathsPrefixLengths[j], proofs[i].A.AuthPathsSuffixes[j])
			authPathsTemp[j] = utilities.Reverse(prevPath)
			for z := 0; z < treeHeight; z++ {
				totalAuthPath[i][j][z] = uints.NewU8Array(authPathsTemp[j][z].KeccakDigest[:])
			}
		}
		totalLeafIndexes[i] = make([]uints.U64, numOfLeavesProved)

		for z := range numOfLeavesProved {
			totalLeafSiblingHashes[i][z] = uints.NewU8Array(proofs[i].A.LeafSiblingHashes[z].KeccakDigest[:])
			totalLeafIndexes[i][z] = uints.NewU64(proofs[i].A.LeafIndexes[z])
			// fmt.Println(proofs[i].B[z])
			for j := range proofs[i].B[z] {
				input := proofs[i].B[z][j]
				// fmt.Println("===============")
				// fmt.Println(j)
				// fmt.Println(input.Limbs)
				// fmt.Println("===============")
				totalLeaves[i][z][j] = typeConverters.LimbsToBigIntMod(input.Limbs)
			}
		}
	}
	startingDomainGen, _ := new(big.Int).SetString(cfg.DomainGenerator, 10)
	mvParamsNumberOfVariables := cfg.NVars
	foldingFactor := cfg.FoldingFactor
	finalSumcheckRounds := mvParamsNumberOfVariables % foldingFactor[0]
	domainSize := (2 << mvParamsNumberOfVariables) * (1 << cfg.Rate) / 2
	oodSamples := cfg.OODSamples
	numOfQueries := cfg.NumQueries
	powBits := cfg.PowBits
	finalQueries := cfg.FinalQueries
	nRounds := cfg.NRounds
	statementPoints := make([][]frontend.Variable, 1)
	statementPoints[0] = make([]frontend.Variable, mvParamsNumberOfVariables)
	contStatementPoints := make([][]frontend.Variable, 1)
	contStatementPoints[0] = make([]frontend.Variable, mvParamsNumberOfVariables)
	for i := range mvParamsNumberOfVariables {
		statementPoints[0][i] = frontend.Variable(0)
		contStatementPoints[0][i] = frontend.Variable(0)
	}

	transcriptT := make([]uints.U8, cfg.TranscriptLen)
	contTranscript := make([]uints.U8, cfg.TranscriptLen)

	for i := range cfg.Transcript {
		transcriptT[i] = uints.NewU8(cfg.Transcript[i])
		contTranscript[i] = uints.NewU8(cfg.Transcript[i])
	}

	linearStatementValuesAtPoints := make([]frontend.Variable, len(proof_arg.StatementValuesAtRandomPoint))
	contLinearStatementValuesAtPoints := make([]frontend.Variable, len(proof_arg.StatementValuesAtRandomPoint))

	linearStatementEvaluations := make([]frontend.Variable, len(cfg.StatementEvaluations))
	contLinearStatementEvaluations := make([]frontend.Variable, len(cfg.StatementEvaluations))
	for i := range len(proof_arg.StatementValuesAtRandomPoint) {
		linearStatementValuesAtPoints[i] = typeConverters.LimbsToBigIntMod(proof_arg.StatementValuesAtRandomPoint[i].Limbs)
		contLinearStatementValuesAtPoints[i] = typeConverters.LimbsToBigIntMod(proof_arg.StatementValuesAtRandomPoint[i].Limbs)
		x, _ := new(big.Int).SetString(cfg.StatementEvaluations[i], 10)
		linearStatementEvaluations[i] = frontend.Variable(x)
		contLinearStatementEvaluations[i] = frontend.Variable(x)
	}

	var circuit = Circuit{
		IO:                                   []byte(cfg.IOPattern),
		Transcript:                           contTranscript,
		RoundParametersOODSamples:            oodSamples,
		RoundParametersNumOfQueries:          numOfQueries,
		StartingDomainBackingDomainGenerator: startingDomainGen,
		ParamNRounds:                         nRounds,
		FoldOptimisation:                     true,
		InitialStatement:                     true,
		CommittmentOODSamples:                1,
		DomainSize:                           domainSize,
		FoldingFactor:                        foldingFactor[0],
		MVParamsNumberOfVariables:            mvParamsNumberOfVariables,
		FinalSumcheckRounds:                  finalSumcheckRounds,
		PowBits:                              powBits,
		FinalPowBits:                         cfg.FinalPowBits,
		FinalFoldingPowBits:                  0,
		FinalQueries:                         finalQueries,
		StatementPoints:                      contStatementPoints,
		StatementEvaluations:                 0,
		LinearStatementEvaluations:           contLinearStatementEvaluations,
		LinearStatementValuesAtPoints:        contLinearStatementValuesAtPoints,
		Leaves:                               containerTotalLeaves,
		LeafIndexes:                          containerTotalLeafIndexes,
		LeafSiblingHashes:                    containerTotalLeafSiblingHashes,
		AuthPaths:                            containerTotalAuthPath,
		NVars:                                cfg.NVars,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	assignment := Circuit{
		IO:                                   []byte(cfg.IOPattern),
		Transcript:                           transcriptT,
		FoldOptimisation:                     true,
		InitialStatement:                     true,
		CommittmentOODSamples:                1,
		DomainSize:                           domainSize,
		StartingDomainBackingDomainGenerator: startingDomainGen,
		FoldingFactor:                        foldingFactor[0],
		PowBits:                              powBits,
		FinalPowBits:                         cfg.FinalPowBits,
		FinalFoldingPowBits:                  0,
		FinalSumcheckRounds:                  finalSumcheckRounds,
		MVParamsNumberOfVariables:            mvParamsNumberOfVariables,
		RoundParametersOODSamples:            oodSamples,
		RoundParametersNumOfQueries:          numOfQueries,
		ParamNRounds:                         nRounds,
		FinalQueries:                         finalQueries,
		StatementPoints:                      statementPoints,
		StatementEvaluations:                 0,
		LinearStatementEvaluations:           linearStatementEvaluations,
		LinearStatementValuesAtPoints:        linearStatementValuesAtPoints,
		Leaves:                               totalLeaves,
		LeafIndexes:                          totalLeafIndexes,
		LeafSiblingHashes:                    totalLeafSiblingHashes,
		AuthPaths:                            totalAuthPath,
		NVars:                                cfg.NVars,
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness, backend.WithSolverOptions(solver.WithHints(utilities.IndexOf)))
	groth16.Verify(proof, vk, publicWitness)
}
