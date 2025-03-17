package main

import (
	"math/bits"
	"reilabs/whir-verifier-circuit/typeConverters"
	"reilabs/whir-verifier-circuit/utilities"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/uints"
	gnark_nimue "github.com/reilabs/gnark-nimue"
	skyscraper "github.com/reilabs/gnark-skyscraper"
)

func calculateEQ(api frontend.API, alphas []frontend.Variable, r []frontend.Variable) frontend.Variable {
	ans := frontend.Variable(1)
	for i, alpha := range alphas {
		ans = api.Mul(ans, api.Add(api.Mul(alpha, r[i]), api.Mul(api.Sub(frontend.Variable(1), alpha), api.Sub(frontend.Variable(1), r[i]))))
	}
	return ans
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
	arthur gnark_nimue.Arthur,
	uapi *uints.BinaryField[uints.U64],
	sc *skyscraper.Skyscraper,
) ([]frontend.Variable, [][][]frontend.Variable, []frontend.Variable, error) {
	if err := FillInAndVerifyRootHash(0, api, uapi, sc, circuit, arthur); err != nil {
		return nil, nil, nil, err
	}

	initialOODQueries := make([]frontend.Variable, circuit.CommittmentOODSamples)
	if err := arthur.FillChallengeScalars(initialOODQueries); err != nil {
		return nil, nil, nil, err
	}

	initialOODAnswers := make([]frontend.Variable, circuit.CommittmentOODSamples)
	if err := arthur.FillNextScalars(initialOODAnswers); err != nil {
		return nil, nil, nil, err
	}

	sumcheckRounds := make([][][]frontend.Variable, circuit.FoldingFactor)

	combinationRandomnessGenerator := make([]frontend.Variable, 1)
	if err := arthur.FillChallengeScalars(combinationRandomnessGenerator); err != nil {
		return nil, nil, nil, err
	}

	initialCombinationRandomness := utilities.ExpandRandomness(api, combinationRandomnessGenerator[0], circuit.CommittmentOODSamples+len(circuit.LinearStatementEvaluations))

	for i := range circuit.FoldingFactor {
		sumcheckRounds[i] = make([][]frontend.Variable, 2)
		sumcheckPolynomialEvals := make([]frontend.Variable, 3)

		if err := arthur.FillNextScalars(sumcheckPolynomialEvals); err != nil {
			return nil, nil, nil, err
		}

		foldingRandomnessSingle := make([]frontend.Variable, 1)
		if err := arthur.FillChallengeScalars(foldingRandomnessSingle); err != nil {
			return nil, nil, nil, err
		}

		sumcheckRounds[i][0] = sumcheckPolynomialEvals
		sumcheckRounds[i][1] = foldingRandomnessSingle
	}

	checkTheVeryFirstSumcheck(api, circuit, initialOODAnswers, initialCombinationRandomness, sumcheckRounds)

	for roundIndex := 1; roundIndex < circuit.FoldingFactor; roundIndex++ {
		evaluatedPolyAtRandomness := utilities.EvaluateQuadraticPolynomialFromEvaluationList(
			api,
			sumcheckRounds[roundIndex-1][0],
			sumcheckRounds[roundIndex-1][1][0],
		)

		utilities.CheckSumOverBool(api, evaluatedPolyAtRandomness, sumcheckRounds[roundIndex][0])
	}

	return initialOODQueries, sumcheckRounds, initialCombinationRandomness, nil
}

func FillInOODPointsAndAnswers(oodPoints *[]frontend.Variable, oodAnswers *[]frontend.Variable, numberOfOODPoints int, arthur gnark_nimue.Arthur) error {
	*oodPoints = make([]frontend.Variable, numberOfOODPoints)
	*oodAnswers = make([]frontend.Variable, numberOfOODPoints)

	if numberOfOODPoints > 0 {
		if err := arthur.FillChallengeScalars(*oodPoints); err != nil {
			return err
		}

		if err := arthur.FillNextScalars(*oodAnswers); err != nil {
			return err
		}
	}

	return nil
}

func RunPoW(api frontend.API, sc *skyscraper.Skyscraper, arthur gnark_nimue.Arthur, difficulty int) error {
	if difficulty > 0 {
		_, _, err := utilities.PoW(api, sc, arthur, difficulty)
		if err != nil {
			return err
		}
	}
	return nil
}

func FillInSumcheckPolynomialsAndRandomnessAndRunPoW(NVars int, arthur gnark_nimue.Arthur, api frontend.API, sc *skyscraper.Skyscraper, NpowBits int) ([][]frontend.Variable, []frontend.Variable, error) {
	finalSumcheckPolynomials := make([][]frontend.Variable, NVars)
	finalSumcheckRandomness := make([]frontend.Variable, NVars)

	for i := range NVars {
		finalSumcheckPolynomials[i] = make([]frontend.Variable, 3) // Sumcheck polynomial in the evaluations form
		finalSumcheckRanomnessTemp := make([]frontend.Variable, 1) // Sumcheck folding randomness

		if err := arthur.FillNextScalars(finalSumcheckPolynomials[i]); err != nil {
			return nil, nil, err
		}

		if err := arthur.FillChallengeScalars(finalSumcheckRanomnessTemp); err != nil {
			return nil, nil, err
		}

		finalSumcheckRandomness[i] = finalSumcheckRanomnessTemp[0]
		if err := RunPoW(api, sc, arthur, NpowBits); err != nil {
			return nil, nil, err
		}
	}

	return finalSumcheckPolynomials, finalSumcheckRandomness, nil
}

func GenerateStirChallengePoints(api frontend.API, arthur gnark_nimue.Arthur, NQueries int, leafIndexes []uints.U64, domainSize int, circuit *Circuit, uapi *uints.BinaryField[uints.U64], expDomainGenerator frontend.Variable) ([]frontend.Variable, error) {
	finalIndexes, err := GetStirChallenges(api, *circuit, arthur, NQueries, domainSize)
	if err != nil {
		api.Println(err)
		return nil, err
	}

	err = utilities.IsSubset(api, uapi, arthur, finalIndexes, leafIndexes)
	if err != nil {
		return nil, err
	}

	finalRandomnessPoints := make([]frontend.Variable, len(leafIndexes))

	for index := range leafIndexes {
		finalRandomnessPoints[index] = utilities.Exponent(api, uapi, expDomainGenerator, leafIndexes[index])
	}

	return finalRandomnessPoints, nil
}

func GenerateCombinationRandomness(api frontend.API, arthur gnark_nimue.Arthur, randomnessLength int) ([]frontend.Variable, error) {
	combRandomnessGen := make([]frontend.Variable, 1)
	if err := arthur.FillChallengeScalars(combRandomnessGen); err != nil {
		return nil, err
	}

	combinationRandomness := utilities.ExpandRandomness(api, combRandomnessGen[0], randomnessLength)
	return combinationRandomness, nil

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
	finalSumcheckPolynomials [][]frontend.Variable,
) {
	computedFolds := ComputeFolds(api, circuit, sumcheckRounds, finalFoldingRandomness)

	prevPoly := sumcheckRounds[len(sumcheckRounds)-1][0][:]
	prevRandomness := sumcheckRounds[len(sumcheckRounds)-1][1][0]

	for roundIndex := range circuit.RoundParametersOODSamples {
		currentValues := make([]frontend.Variable, len(computedFolds[roundIndex])+1)
		currentValues[0] = oodAnswersList[roundIndex][0]
		copy(currentValues[1:], computedFolds[roundIndex][:])
		valuesTimesCombRand := utilities.DotProduct(api, currentValues, combinationRandomness[roundIndex])

		claimedSum := api.Add(utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, prevPoly, prevRandomness), valuesTimesCombRand)

		utilities.CheckSumOverBool(api, claimedSum, sumcheckPolynomials[roundIndex][0])

		prevPoly = sumcheckPolynomials[roundIndex][0][:]
		for polyIndex := 1; polyIndex < len(sumcheckPolynomials[roundIndex]); polyIndex++ {
			eval := utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, sumcheckPolynomials[roundIndex][polyIndex-1], finalFoldingRandomness[roundIndex][polyIndex-1])

			utilities.CheckSumOverBool(api, eval, sumcheckPolynomials[roundIndex][polyIndex])

			prevPoly = sumcheckPolynomials[roundIndex][polyIndex]
			prevRandomness = finalFoldingRandomness[roundIndex][polyIndex]
		}

	}

	lastEval := utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, prevPoly, prevRandomness)

	finalEvaluations := utilities.UnivarPoly(api, finalCoefficients, finalRandomnessPoints)

	finalFolds := computedFolds[len(computedFolds)-1]
	for foldIndex := range finalFolds {
		api.AssertIsEqual(finalFolds[foldIndex], finalEvaluations[foldIndex])
	}

	if circuit.FinalSumcheckRounds > 0 {
		utilities.CheckSumOverBool(api, lastEval, finalSumcheckPolynomials[0])

		for round := 1; round < len(finalSumcheckPolynomials); round++ {
			eval := utilities.EvaluateQuadraticPolynomialFromEvaluationList(api, finalSumcheckPolynomials[round-1], finalSumcheckRandomness[round-1])
			utilities.CheckSumOverBool(api, eval, finalSumcheckPolynomials[round])
		}

		lastEval = utilities.EvaluateQuadraticPolynomialFromEvaluationList(
			api,
			finalSumcheckPolynomials[len(finalSumcheckPolynomials)-1],
			finalSumcheckRandomness[len(finalSumcheckPolynomials)-1],
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

func SumcheckForR1CSIOP(api frontend.API, arthur gnark_nimue.Arthur, circuit *Circuit) ([]frontend.Variable, []frontend.Variable, frontend.Variable, error) {
	t_rand := make([]frontend.Variable, circuit.NVars)
	sp_rand := make([]frontend.Variable, circuit.NVars)
	savedValForSumcheck := frontend.Variable(0)

	err := arthur.FillChallengeScalars(t_rand)
	if err != nil {
		return nil, nil, nil, err
	}

	sp_rand_temp := make([]frontend.Variable, 1)
	for i := 0; i < circuit.NVars; i++ {
		sp := make([]frontend.Variable, 4)
		if err = arthur.FillNextScalars(sp); err != nil {
			return nil, nil, nil, err
		}
		if err = arthur.FillChallengeScalars(sp_rand_temp); err != nil {
			return nil, nil, nil, err
		}
		sp_rand[i] = sp_rand_temp[0]
		sumcheckVal := api.Add(utilities.UnivarPoly(api, sp, []frontend.Variable{0})[0], utilities.UnivarPoly(api, sp, []frontend.Variable{1})[0])
		api.AssertIsEqual(sumcheckVal, savedValForSumcheck)
		savedValForSumcheck = utilities.UnivarPoly(api, sp, []frontend.Variable{sp_rand[i]})[0]
	}

	return t_rand, sp_rand, savedValForSumcheck, nil
}

func FillInAndVerifyRootHash(roundNum int, api frontend.API, uapi *uints.BinaryField[uints.U64], sc *skyscraper.Skyscraper, circuit *Circuit, arthur gnark_nimue.Arthur) error {
	rootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(rootHash); err != nil {
		return err
	}
	err := VerifyMerkleTreeProofs(api, uapi, sc, circuit.LeafIndexes[roundNum], circuit.Leaves[roundNum], circuit.LeafSiblingHashes[roundNum], circuit.AuthPaths[roundNum], rootHash[0])
	if err != nil {
		return err
	}
	return nil
}

func generateFinalCoefficientsAndRandomnessPoints(api frontend.API, arthur gnark_nimue.Arthur, circuit *Circuit, uapi *uints.BinaryField[uints.U64], sc *skyscraper.Skyscraper, domainSize int, expDomainGenerator frontend.Variable) ([]frontend.Variable, []frontend.Variable, error) {
	finalCoefficients := make([]frontend.Variable, 1<<circuit.FinalSumcheckRounds)
	if err := arthur.FillNextScalars(finalCoefficients); err != nil {
		return nil, nil, err
	}
	finalRandomnessPoints, err := GenerateStirChallengePoints(api, arthur, circuit.FinalQueries, circuit.LeafIndexes[len(circuit.LeafIndexes)-1], domainSize, circuit, uapi, expDomainGenerator)
	if err != nil {
		return nil, nil, err
	}
	if err := RunPoW(api, sc, arthur, circuit.FinalPowBits); err != nil {
		return nil, nil, err
	}
	return finalCoefficients, finalRandomnessPoints, nil
}

func initializeComponents(api frontend.API, circuit *Circuit) (*skyscraper.Skyscraper, gnark_nimue.Arthur, *uints.BinaryField[uints.U64], error) {
	sc := skyscraper.NewSkyscraper(api, 2)
	arthur, err := gnark_nimue.NewSkyscraperArthur(api, sc, circuit.IO, circuit.Transcript[:])
	if err != nil {
		return nil, nil, nil, err
	}
	uapi, err := uints.New[uints.U64](api)
	if err != nil {
		return nil, nil, nil, err
	}
	return sc, arthur, uapi, nil
}
