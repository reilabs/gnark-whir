package main

import (
	"fmt"
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
	"github.com/consensys/gnark/std/lookup/logderivlookup"
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
	// Public Input
	IO         []byte
	Transcript [3104]uints.U8 `gnark:",public"`
}

func IndexOf(_ *big.Int, inputs []*big.Int, outputs []*big.Int) error {
	if len(outputs) != 1 {
		return fmt.Errorf("expecting one output")
	}

	if len(inputs) == 0 {
		return fmt.Errorf("inputs array cannot be empty")
	}

	target := inputs[0]

	for i := 1; i < len(inputs); i++ {
		if inputs[i].Cmp(target) == 0 {
			outputs[0] = big.NewInt(int64(i - 1))
			return nil
		}
	}

	outputs[0] = big.NewInt(-1)
	return nil
}

func PoW(api frontend.API, arthur gnark_nimue.Arthur) ([]uints.U8, []uints.U8, error) {
	challenge := make([]uints.U8, 32)
	err := arthur.FillChallengeBytes(challenge)
	if err != nil {
		return nil, nil, err
	}
	// api.Println(challenge)
	nonce := make([]uints.U8, 8)
	err = arthur.FillNextBytes(nonce)
	if err != nil {
		return nil, nil, err
	}
	// api.Println(nonce)
	return challenge, nonce, nil
}

func GetStirChallenges(api frontend.API, circuit Circuit, arthur gnark_nimue.Arthur, numQueries int, domainSize int) ([]frontend.Variable, error) {
	foldedDomainSize := domainSize / (1 << circuit.FoldingFactor)
	domainSizeBytes := (bits.Len(uint(foldedDomainSize*2-1)) - 1 + 7) / 8
	stirQueries := make([]uints.U8, domainSizeBytes*numQueries)
	// api.Println(domainSizeBytes * numQueries)
	err := arthur.FillChallengeBytes(stirQueries)
	if err != nil {
		return nil, err
	}
	indexes := make([]frontend.Variable, numQueries)
	bitLength := bits.Len(uint(foldedDomainSize)) - 1

	for i := range numQueries {
		tmpRes := frontend.Variable(0)
		for j := range domainSizeBytes {
			tmpRes = api.Add(stirQueries[j+i*domainSizeBytes].Val, api.Mul(tmpRes, 256))
		}
		bitsOfTmpRes := api.ToBinary(tmpRes)
		indexes[i] = api.FromBinary(bitsOfTmpRes[0:bitLength]...)
	}
	return indexes, nil
}

func IsSubset(api frontend.API, uapi *uints.BinaryField[uints.U64], circuit Circuit, arthur gnark_nimue.Arthur, indexes []frontend.Variable, merkleIndexes []uints.U64) error {
	dedupedLUT := logderivlookup.New(api)
	inputArr := make([]frontend.Variable, len(merkleIndexes)+1)

	for j, index := range merkleIndexes {
		dedupedLUT.Insert(uapi.ToValue(index))
		inputArr[1+j] = uapi.ToValue(index)
	}

	for _, x := range indexes {
		inputArr[0] = x
		res, newerr := api.Compiler().NewHint(IndexOf, 1, inputArr...)
		if newerr != nil {
			return newerr
		}
		searchRes := dedupedLUT.Lookup(res[0])
		api.AssertIsEqual(x, searchRes[0])
	}
	return nil
}

func VerifyMerkleTreeProofs(api frontend.API, uapi *uints.BinaryField[uints.U64], sc *skyscraper.Skyscraper, leafIndexes []uints.U64, leaves [][]frontend.Variable, leafSiblingHashes [][]uints.U8, authPaths [][][]uints.U8, rootHash frontend.Variable) error {
	numOfLeavesProved := len(leaves)
	for i := range numOfLeavesProved {
		treeHeight := len(authPaths[i]) + 1
		leafIndex := api.ToBinary(uapi.ToValue(leafIndexes[i]), treeHeight)
		leafSiblingHash := typeConverters.LittleEndianFromUints(api, leafSiblingHashes[i])

		claimedLeafHash := sc.Compress(leaves[i][0], leaves[i][1])
		for x := range len(leaves[i]) - 2 {
			claimedLeafHash = sc.Compress(claimedLeafHash, leaves[i][x+2])
		}

		dir := leafIndex[0]

		x_leftChild := api.Select(dir, leafSiblingHash, claimedLeafHash)
		x_rightChild := api.Select(dir, claimedLeafHash, leafSiblingHash)

		currentHash := sc.Compress(x_leftChild, x_rightChild)

		for level := 1; level < treeHeight; level++ {
			index := leafIndex[level]

			siblingHash := typeConverters.LittleEndianFromUints(api, authPaths[i][level-1])

			dir := api.And(index, 1)
			left := api.Select(dir, siblingHash, currentHash)
			right := api.Select(dir, currentHash, siblingHash)

			currentHash = sc.Compress(left, right)
		}
		api.AssertIsEqual(currentHash, rootHash)
	}
	return nil
}

func ExpandRandomness(api frontend.API, base frontend.Variable, len int) []frontend.Variable {
	res := make([]frontend.Variable, len)
	acc := frontend.Variable(1)
	for i := range len {
		res[i] = acc
		acc = api.Mul(acc, base)
	}
	return res
}

func ExpandFromUnivariate(api frontend.API, base frontend.Variable, len int) []frontend.Variable {
	res := make([]frontend.Variable, len)
	acc := base
	for i := range len {
		res[len-1-i] = acc
		acc = api.Mul(acc, acc)
	}
	return res
}

func checkTheVeryFirstSumcheck(api frontend.API, firstOODAnswers []frontend.Variable, initialCombinationRandomness []frontend.Variable, sumcheckRounds [][][]frontend.Variable) {
	plugInEvaluation := frontend.Variable(0)
	for i := range initialCombinationRandomness {
		if i < len(firstOODAnswers) {
			plugInEvaluation = api.Add(
				plugInEvaluation,
				api.Mul(initialCombinationRandomness[i], firstOODAnswers[i]),
			)
		}
	}
	checkSumOverBool(api, plugInEvaluation, sumcheckRounds[0][0])
}

func evaluateFunction(api frontend.API, evaluations []frontend.Variable, point frontend.Variable) (ans frontend.Variable) {
	inv2 := api.Inverse(2)
	b0 := evaluations[0]
	b1 := api.Mul(api.Add(api.Neg(evaluations[2]), api.Mul(4, evaluations[1]), api.Mul(-3, evaluations[0])), inv2)
	b2 := api.Mul(api.Add(evaluations[2], api.Mul(-2, evaluations[1]), evaluations[0]), inv2)
	return api.Add(api.Mul(point, point, b2), api.Mul(point, b1), b0)
}

func checkSumOverBool(api frontend.API, value frontend.Variable, polyEvals []frontend.Variable) {
	sumOverBools := api.Add(polyEvals[0], polyEvals[1])
	api.AssertIsEqual(value, sumOverBools)
}

func initialSumcheck(api frontend.API, circuit *Circuit, firstOODAnswers []frontend.Variable, initialCombinationRandomness []frontend.Variable, sumcheckRounds [][][]frontend.Variable) {
	checkTheVeryFirstSumcheck(api, firstOODAnswers, initialCombinationRandomness, sumcheckRounds)
	for i := 1; i < circuit.FoldingFactor; i++ {
		randEval := evaluateFunction(api, sumcheckRounds[i-1][0], sumcheckRounds[i-1][1][0])
		checkSumOverBool(api, randEval, sumcheckRounds[i][0])
	}
}

func checkMainRounds(api frontend.API, circuit *Circuit, sumcheckRounds [][][]frontend.Variable, sumcheckPolynomials [][][]frontend.Variable, finalFoldingRandomness [][]frontend.Variable, oodPointsList [][]frontend.Variable, oodAnswersList [][]frontend.Variable, combinationRandomness [][]frontend.Variable, finalCoefficients []frontend.Variable, finalRandomnessPoints []frontend.Variable, initialOODQueries []frontend.Variable, initialCombinationRandomness []frontend.Variable, stirChallengesPoints [][]frontend.Variable, perRoundCombinationRandomness [][]frontend.Variable, finalSumcheckRandomness []frontend.Variable, finalSumcheckRounds [][][]frontend.Variable) {
	computedFolds := ComputeFolds(api, circuit, sumcheckRounds, finalFoldingRandomness)
	lastEval := frontend.Variable(0)
	prevPoly := sumcheckRounds[1][0][:]
	prevRandomness := sumcheckRounds[1][1][0]
	for r := range circuit.RoundParametersOODSamples {
		values := make([]frontend.Variable, len(computedFolds[r])+1)
		values[0] = oodAnswersList[r][0]
		for z := 1; z < len(values); z++ {
			values[z] = computedFolds[r][z-1]
		}
		valuesTimesCombRand := frontend.Variable(0)
		for i := range values {
			product := api.Mul(values[i], combinationRandomness[r][i])
			valuesTimesCombRand = api.Add(valuesTimesCombRand, product)
		}

		claimedSum := api.Add(evaluateFunction(api, prevPoly, prevRandomness), valuesTimesCombRand)
		checkSumOverBool(api, claimedSum, sumcheckPolynomials[r][0])

		prevPoly = sumcheckPolynomials[r][0][:]
		for i := 1; i < len(sumcheckPolynomials[r]); i++ {
			eval := evaluateFunction(api, sumcheckPolynomials[r][i-1], finalFoldingRandomness[r][i-1])
			lastEval = eval
			checkSumOverBool(api, eval, sumcheckPolynomials[r][i])
			prevPoly = sumcheckPolynomials[r][i]
			prevRandomness = finalFoldingRandomness[r][i]
		}
		lastEval = evaluateFunction(api, sumcheckPolynomials[r][len(sumcheckPolynomials[r])-1], finalFoldingRandomness[r][len(sumcheckPolynomials[r])-1])
	}
	finalEvaluations := utilities.UnivarPoly(api, finalCoefficients, finalRandomnessPoints)
	for fold := range computedFolds[len(computedFolds)-1] {
		api.AssertIsEqual(computedFolds[len(computedFolds)-1][fold], finalEvaluations[fold])
	}
	if circuit.FinalSumcheckRounds > 0 {
		checkSumOverBool(api, lastEval, finalSumcheckRounds[0][0])

		for i := 1; i < len(finalSumcheckRounds); i++ {
			eval := evaluateFunction(api, finalSumcheckRounds[i-1][0], finalSumcheckRounds[i-1][0])
			lastEval = eval
			checkSumOverBool(api, eval, finalSumcheckRounds[i][0])
		}
		lastEval = evaluateFunction(api, finalSumcheckRounds[len(finalSumcheckRounds)-1][0], finalSumcheckRounds[len(finalSumcheckRounds)-1][1][0])
	}
	evaluationOfVPoly := ComputeVPoly(api, circuit, finalFoldingRandomness, sumcheckRounds, initialOODQueries, circuit.StatementPoints, initialCombinationRandomness, oodPointsList, stirChallengesPoints, perRoundCombinationRandomness, finalSumcheckRandomness)
	api.AssertIsEqual(lastEval, api.Mul(evaluationOfVPoly, utilities.MultivarPoly(finalCoefficients, finalSumcheckRandomness, api)))
}

func ComputeVPoly(api frontend.API, circuit *Circuit, finalFoldingRandomness [][]frontend.Variable, sumcheckRounds [][][]frontend.Variable, initialOODQueries []frontend.Variable, statementPoints [][]frontend.Variable, initialCombinationRandomness []frontend.Variable, oodPointLists [][]frontend.Variable, stirChallengesPoints [][]frontend.Variable, perRoundCombinationRandomness [][]frontend.Variable, finalSumcheckRandomness []frontend.Variable) frontend.Variable {
	foldingRandomness := make([]frontend.Variable, len(finalFoldingRandomness[0])*len(finalFoldingRandomness)+len(sumcheckRounds)+len(finalSumcheckRandomness))
	for j := range len(finalSumcheckRandomness) {
		foldingRandomness[j] = finalSumcheckRandomness[j]
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

	tmpArr := make([][]frontend.Variable, len(initialOODQueries)+len(statementPoints))
	numVariables := circuit.MVParamsNumberOfVariables
	for j := range initialOODQueries {
		tmpArr[j] = ExpandFromUnivariate(api, initialOODQueries[j], numVariables)
	}
	for j := range statementPoints {
		tmpArr[len(initialOODQueries)+j] = statementPoints[j]
	}
	value := frontend.Variable(0)
	for j := range tmpArr {
		value = api.Add(value, api.Mul(initialCombinationRandomness[j], EqPolyOutside(api, tmpArr[j], foldingRandomness)))
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
			point := ExpandFromUnivariate(api, newTmpArr[i], numberVars)
			sumOfClaims = api.Add(sumOfClaims, api.Mul(EqPolyOutside(api, point, foldingRandomness[0:numberVars]), perRoundCombinationRandomness[r][i]))
		}
		value = api.Add(value, sumOfClaims)
	}

	return value
}

func EqPolyOutside(api frontend.API, coords []frontend.Variable, point []frontend.Variable) frontend.Variable {
	acc := frontend.Variable(1)
	for i := range coords {
		acc = api.Mul(acc, api.Add(api.Mul(coords[i], point[i]), api.Mul(api.Sub(frontend.Variable(1), coords[i]), api.Sub(frontend.Variable(1), point[i]))))
	}
	return acc
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

	finalFoldingRandomness := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	sumcheckPolynomials := make([][][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	oodPointsList := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	oodAnswersList := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	perRoundCombinationRandomness := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	exp := uint64(1 << circuit.FoldingFactor)
	expDomainGenerator := Exponent(api, uapi, circuit.StartingDomainBackingDomainGenerator, uints.NewU64(exp))
	domainSize := circuit.DomainSize

	rootHash := make([]frontend.Variable, 1)
	err = arthur.FillNextScalars(rootHash)
	if err != nil {
		return err
	}
	initialOODQueries := make([]frontend.Variable, circuit.CommittmentOODSamples)
	err = arthur.FillChallengeScalars(initialOODQueries)

	if err != nil {
		return err
	}

	initialOODAnswers := make([]frontend.Variable, circuit.CommittmentOODSamples)
	err = arthur.FillNextScalars(initialOODAnswers)

	if err != nil {
		return err
	}

	initialCombinationRandomness := make([]frontend.Variable, 1)
	// if circuit.InitialStatement {
	combinationRandomnessGenerator := make([]frontend.Variable, 1)
	err = arthur.FillChallengeScalars(combinationRandomnessGenerator)
	if err != nil {
		return err
	}

	initialCombinationRandomness = make([]frontend.Variable, circuit.CommittmentOODSamples+len(circuit.StatementPoints))
	initialCombinationRandomness = ExpandRandomness(api, combinationRandomnessGenerator[0], circuit.CommittmentOODSamples+len(circuit.StatementPoints))

	sumcheckRounds := make([][][]frontend.Variable, circuit.FoldingFactor)
	for i := range circuit.FoldingFactor {
		sumcheckRounds[i] = make([][]frontend.Variable, 2)
		sumcheckPolynomialEvals := make([]frontend.Variable, 3)
		err = arthur.FillNextScalars(sumcheckPolynomialEvals)
		if err != nil {
			return err
		}

		foldingRandomnessSingle := make([]frontend.Variable, 1)
		err = arthur.FillChallengeScalars(foldingRandomnessSingle)

		if err != nil {
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
		err = arthur.FillNextScalars(roots[r])
		if err != nil {
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
			err = arthur.FillChallengeScalars(oodPoints)
			if err != nil {
				return err
			}
			err = arthur.FillNextScalars(oodAnswers)
			if err != nil {
				return err
			}

			oodPointsList[r] = oodPoints
			oodAnswersList[r] = oodAnswers
		}

		indexes, err := GetStirChallenges(api, *circuit, arthur, circuit.RoundParametersNumOfQueries[r], domainSize)
		if err != nil {
			return err
		}

		err = IsSubset(api, uapi, *circuit, arthur, indexes, circuit.LeafIndexes[r])
		if err != nil {
			return err
		}
		stirChallengesPoints[r] = make([]frontend.Variable, len(circuit.LeafIndexes[r]))

		for index := range circuit.LeafIndexes[r] {
			x := Exponent(api, uapi, expDomainGenerator, circuit.LeafIndexes[r][index])
			stirChallengesPoints[r][index] = x
		}
		// api.Println(circuit.PowBytes)
		if circuit.PowBits[r] > 0 {
			_, _, err := PoW(api, arthur)
			if err != nil {
				return err
			}
			// api.Println(challenge)
			// api.Println(nonce)
		}
		combRandomnessGen := make([]frontend.Variable, 1)
		err = arthur.FillChallengeScalars(combRandomnessGen)
		if err != nil {
			return err
		}
		// api.Println(combRandomnessGen...)
		combinationRandomness := ExpandRandomness(api, combRandomnessGen[0], len(circuit.LeafIndexes[r])+circuit.RoundParametersOODSamples[r])
		// api.Println(combinationRandomness...)
		perRoundCombinationRandomness[r] = combinationRandomness
		finalFoldingRandomness[r] = make([]frontend.Variable, circuit.FoldingFactor)
		sumcheckPolynomials[r] = make([][]frontend.Variable, circuit.FoldingFactor)
		for i := range circuit.FoldingFactor {
			sumcheckPoly := make([]frontend.Variable, 3)
			err = arthur.FillNextScalars(sumcheckPoly)
			if err != nil {
				return err
			}
			sumcheckPolynomials[r][i] = sumcheckPoly
			// api.Println(sumcheckPoly)
			foldingRandomnessSingle := make([]frontend.Variable, 1)
			err = arthur.FillChallengeScalars(foldingRandomnessSingle)
			if err != nil {
				return err
			}
			finalFoldingRandomness[r][i] = foldingRandomnessSingle[0]
		}

		domainSize /= 2
		expDomainGenerator = api.Mul(expDomainGenerator, expDomainGenerator)
	}
	// api.Println(finalFoldingRandomness...)

	finalCoefficients := make([]frontend.Variable, 1<<circuit.FinalSumcheckRounds)
	err = arthur.FillNextScalars(finalCoefficients)
	if err != nil {
		return err
	}
	// api.Println(finalCoefficients...)

	finalIndexes, err := GetStirChallenges(api, *circuit, arthur, circuit.FinalQueries, domainSize)
	if err != nil {
		api.Println(err)
		return nil
	}
	// api.Println(finalIndexes)
	err = IsSubset(api, uapi, *circuit, arthur, finalIndexes, circuit.LeafIndexes[len(circuit.LeafIndexes)-1])
	if err != nil {
		return err
	}

	finalRandomnessPoints := make([]frontend.Variable, len(circuit.LeafIndexes[len(circuit.LeafIndexes)-1]))

	for index := range circuit.LeafIndexes[len(circuit.LeafIndexes)-1] {
		finalRandomnessPoints[index] = Exponent(api, uapi, expDomainGenerator, circuit.LeafIndexes[len(circuit.LeafIndexes)-1][index])
	}

	err = VerifyMerkleTreeProofs(api, uapi, sc, circuit.LeafIndexes[len(circuit.LeafIndexes)-1], circuit.Leaves[len(circuit.LeafIndexes)-1], circuit.LeafSiblingHashes[len(circuit.LeafIndexes)-1], circuit.AuthPaths[len(circuit.LeafIndexes)-1], prevRoot)
	if err != nil {
		return err
	}
	if circuit.FinalPowBits > 0 {
		_, _, err := PoW(api, arthur)
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
		err = arthur.FillNextScalars(finalSumcheckPolyEvals)
		if err != nil {
			return err
		}
		finalFoldingRandomnessSingle := make([]frontend.Variable, 1)
		err = arthur.FillChallengeScalars(finalFoldingRandomnessSingle)
		if err != nil {
			return err
		}

		finalSumcheckRounds[i] = make([][]frontend.Variable, 2)
		finalSumcheckRounds[i][0] = finalSumcheckPolyEvals
		finalSumcheckRounds[i][1] = finalFoldingRandomnessSingle
		finalSumcheckRandomness[i] = finalFoldingRandomnessSingle[0]
		if circuit.FinalFoldingPowBits > 0 {
			PoW(api, arthur)
		}
	}

	checkMainRounds(api, circuit, sumcheckRounds, sumcheckPolynomials, finalFoldingRandomness, oodPointsList, oodAnswersList, perRoundCombinationRandomness, finalCoefficients, finalRandomnessPoints, initialOODQueries, initialCombinationRandomness, stirChallengesPoints, perRoundCombinationRandomness, finalSumcheckRandomness, finalSumcheckRounds)
	return nil
}

func Exponent(api frontend.API, uapi *uints.BinaryField[uints.U64], X frontend.Variable, Y uints.U64) frontend.Variable {
	output := frontend.Variable(1)
	bits := api.ToBinary(uapi.ToValue(Y))
	multiply := frontend.Variable(X)
	for i := range bits {
		output = api.Select(bits[i], api.Mul(output, multiply), output)
		multiply = api.Mul(multiply, multiply)
	}
	return output
}

func prefixDecodePath[T any](prevPath []T, prefixLen uint64, suffix []T) []T {
	if prefixLen == 0 {
		res := make([]T, len(suffix))
		copy(res, suffix)
		return res
	} else {
		res := make([]T, prefixLen+uint64(len(suffix)))
		copy(res, prevPath[:prefixLen])
		copy(res[prefixLen:], suffix)
		return res
	}
}

func reverse[T any](s []T) []T {
	res := make([]T, len(s))
	copy(res, s)
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		res[i], res[j] = s[j], s[i]
	}
	return res
}

func verify_circuit(proofs []ProofElement, io string, transcript [3104]uints.U8) {
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
			totalLeaves[i][j] = make([]frontend.Variable, 4)
			containerTotalLeaves[i][j] = make([]frontend.Variable, 4)
			totalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
			containerTotalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
		}

		containerTotalLeafIndexes[i] = make([]uints.U64, numOfLeavesProved)

		var authPathsTemp = make([][]KeccakDigest, numOfLeavesProved)
		var prevPath = proofs[i].A.AuthPathsSuffixes[0]
		authPathsTemp[0] = reverse(prevPath)

		for j := range totalAuthPath[i][0] {
			totalAuthPath[i][0][j] = uints.NewU8Array(authPathsTemp[0][j].KeccakDigest[:])
		}

		for j := 1; j < numOfLeavesProved; j++ {
			prevPath = prefixDecodePath(prevPath, proofs[i].A.AuthPathsPrefixLengths[j], proofs[i].A.AuthPathsSuffixes[j])
			authPathsTemp[j] = reverse(prevPath)
			for z := 0; z < treeHeight; z++ {
				totalAuthPath[i][j][z] = uints.NewU8Array(authPathsTemp[j][z].KeccakDigest[:])
			}
		}
		totalLeafIndexes[i] = make([]uints.U64, numOfLeavesProved)

		for z := range numOfLeavesProved {
			totalLeafSiblingHashes[i][z] = uints.NewU8Array(proofs[i].A.LeafSiblingHashes[z].KeccakDigest[:])
			totalLeafIndexes[i][z] = uints.NewU64(proofs[i].A.LeafIndexes[z])
			for j := range proofs[i].B[z] {
				input := proofs[i].B[z][j]
				totalLeaves[i][z][j] = typeConverters.LimbsToBigIntMod(input.Limbs)
			}
		}
	}
	startingDomainGen, _ := new(big.Int).SetString("19200870435978225707111062059747084165650991997241425080699860725083300967194", 10)
	mvParamsNumberOfVariables := 24
	foldingFactor := 2
	finalSumcheckRounds := mvParamsNumberOfVariables % foldingFactor
	domainSize := 33554432
	var circuit = Circuit{
		IO:                                   []byte(io),
		RoundParametersOODSamples:            []int{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
		RoundParametersNumOfQueries:          []int{100, 50, 34, 25, 20, 17, 15, 13, 12, 10, 10},
		StartingDomainBackingDomainGenerator: startingDomainGen,
		ParamNRounds:                         11,
		FoldOptimisation:                     true,
		InitialStatement:                     true,
		CommittmentOODSamples:                1,
		DomainSize:                           domainSize,
		FoldingFactor:                        foldingFactor,
		MVParamsNumberOfVariables:            mvParamsNumberOfVariables,
		FinalSumcheckRounds:                  finalSumcheckRounds,
		PowBits:                              []int{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		FinalPowBits:                         0,
		FinalFoldingPowBits:                  0,
		FinalQueries:                         9,
		StatementPoints:                      [][]frontend.Variable{{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
		StatementEvaluations:                 0,
		Leaves:                               containerTotalLeaves,
		LeafIndexes:                          containerTotalLeafIndexes,
		LeafSiblingHashes:                    containerTotalLeafSiblingHashes,
		AuthPaths:                            containerTotalAuthPath,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	assignment := Circuit{
		IO:                                   []byte(io),
		Transcript:                           transcript,
		FoldOptimisation:                     true,
		InitialStatement:                     true,
		CommittmentOODSamples:                1,
		DomainSize:                           domainSize,
		StartingDomainBackingDomainGenerator: startingDomainGen,
		FoldingFactor:                        foldingFactor,
		PowBits:                              []int{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		FinalPowBits:                         0,
		FinalFoldingPowBits:                  0,
		FinalSumcheckRounds:                  finalSumcheckRounds,
		MVParamsNumberOfVariables:            mvParamsNumberOfVariables,
		RoundParametersOODSamples:            []int{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
		RoundParametersNumOfQueries:          []int{100, 50, 34, 25, 20, 17, 15, 13, 12, 10, 10},
		ParamNRounds:                         11,
		FinalQueries:                         9,
		StatementPoints:                      [][]frontend.Variable{{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
		StatementEvaluations:                 0,
		Leaves:                               totalLeaves,
		LeafIndexes:                          totalLeafIndexes,
		LeafSiblingHashes:                    totalLeafSiblingHashes,
		AuthPaths:                            totalAuthPath,
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness, backend.WithSolverOptions(solver.WithHints(IndexOf)))
	groth16.Verify(proof, vk, publicWitness)
}
