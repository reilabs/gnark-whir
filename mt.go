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
	"github.com/consensys/gnark/std/hash/sha3"
	"github.com/consensys/gnark/std/lookup/logderivlookup"
	"github.com/consensys/gnark/std/math/uints"
	gnark_nimue "github.com/reilabs/gnark-nimue"
)

type VerifyMerkleProofCircuit struct {
	// Inputs
	DomainSize                  int
	CommittmentOODSamples       int
	FoldingFactor               int
	FinalSumcheckRounds         int
	ParamNRounds                int
	RoundParametersOODSamples   []int
	RoundParametersNumOfQueries []int
	FoldOptimisation            bool
	PowBytes                    int
	FinalPowBytes               int
	FinalQueries                int
	Leaves                      [][][]uints.U8
	LeafIndexes                 [][]uints.U8
	LeafSiblingHashes           [][][]uints.U8
	AuthPaths                   [][][][]uints.U8
	StatementPoints             [][]int
	StatementEvaluations        int
	// Public Input
	IO         []byte
	Transcript [560]uints.U8 `gnark:",public"`
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
	nonce := make([]uints.U8, 8)
	err = arthur.FillNextBytes(nonce)
	if err != nil {
		return nil, nil, err
	}
	return challenge, nonce, nil
}

func GetStirChallenges(api frontend.API, circuit VerifyMerkleProofCircuit, arthur gnark_nimue.Arthur, numQueries int, domainSize int) ([]frontend.Variable, error) {
	foldedDomainSize := domainSize / (1 << circuit.FoldingFactor)
	domainSizeBytes := (bits.Len(uint(foldedDomainSize*2-1)) - 1 + 7) / 8

	stirQueries := make([]uints.U8, domainSizeBytes*numQueries)
	api.Println(numQueries * domainSizeBytes)
	err := arthur.FillChallengeBytes(stirQueries)
	if err != nil {
		return nil, err
	}
	api.Println(stirQueries)
	api.Println(foldedDomainSize)

	indexes := make([]frontend.Variable, numQueries)

	bitLength := bits.Len(uint(foldedDomainSize)) - 1
	api.Println(bitLength)

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

func IsSubset(api frontend.API, circuit VerifyMerkleProofCircuit, arthur gnark_nimue.Arthur, indexes []frontend.Variable, merkleIndexes []uints.U8) error {
	dedupedLUT := logderivlookup.New(api)
	inputArr := make([]frontend.Variable, len(merkleIndexes)+1)

	for j, index := range merkleIndexes {
		dedupedLUT.Insert(index.Val)
		inputArr[1+j] = index.Val
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

func VerifyMerkleTreeProofs(api frontend.API, leafIndexes []uints.U8, leaves [][]uints.U8, leafSiblingHashes [][]uints.U8, authPaths [][][]uints.U8, rootHash []uints.U8) error {
	numOfLeavesProved := len(leaves)
	keccakCount := 0

	for i := 0; i < numOfLeavesProved; i++ {
		treeHeight := len(authPaths[i]) + 1

		leafIndex := api.ToBinary(leafIndexes[i].Val, treeHeight)
		leafSiblingHash := leafSiblingHashes[i]
		keccak, _ := sha3.NewLegacyKeccak256(api)

		keccak.Write(leaves[i])
		claimedLeafHash := keccak.Sum()
		keccakCount += 1
		dir := leafIndex[0]
		// api.Println(dir)

		x_leftChild := make([]uints.U8, 32)
		x_rightChild := make([]uints.U8, 32)

		for j := 0; j < 32; j++ {
			x_leftChild[j].Val = api.Select(dir, leafSiblingHash[j].Val, claimedLeafHash[j].Val)
			x_rightChild[j].Val = api.Select(dir, claimedLeafHash[j].Val, leafSiblingHash[j].Val)
		}

		// api.Println(x_leftChild)
		// api.Println(x_rightChild)
		keccak_new, _ := sha3.NewLegacyKeccak256(api)

		tmp := append(x_leftChild, x_rightChild...)
		keccak_new.Write(tmp)
		currentHash := keccak_new.Sum()
		keccakCount += 1

		// api.Println(currentHash)

		for level := 1; level < treeHeight; level++ {
			index := leafIndex[level]

			siblingHash := authPaths[i][level-1]

			dir := api.And(index, 1)
			left := make([]uints.U8, 32)
			right := make([]uints.U8, 32)

			for z := 0; z < 32; z++ {
				left[z].Val = api.Select(dir, siblingHash[z].Val, currentHash[z].Val)
				right[z].Val = api.Select(dir, currentHash[z].Val, siblingHash[z].Val)
			}

			// api.Println(left)
			// api.Println(right)

			new_tmp := append(left, right...)
			keccak, _ := sha3.NewLegacyKeccak256(api)
			keccak.Write(new_tmp)
			currentHash = keccak.Sum()
			keccakCount += 1
			// api.Println(currentHash)
		}

		for z := 0; z < 32; z++ {
			api.AssertIsEqual(currentHash[z].Val, rootHash[z].Val)
		}
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

func checkTheVeryFirstSumcheck(api frontend.API, circuit *VerifyMerkleProofCircuit, firstOODAnswers []frontend.Variable, randomnessGenerator frontend.Variable, sumcheckRounds [][][]frontend.Variable) {
	initialCombinationRandomness := ExpandRandomness(api, randomnessGenerator, circuit.CommittmentOODSamples+len(circuit.StatementPoints))
	plugInEvaluation := frontend.Variable(0)
	for i := 0; i < len(initialCombinationRandomness); i++ {
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

func initialSumcheck(api frontend.API, circuit *VerifyMerkleProofCircuit, firstOODAnswers []frontend.Variable, randomnessGenerator frontend.Variable, sumcheckRounds [][][]frontend.Variable) {
	checkTheVeryFirstSumcheck(api, circuit, firstOODAnswers, randomnessGenerator, sumcheckRounds)
	for i := 1; i < circuit.FoldingFactor; i++ {
		api.Println(sumcheckRounds[i-1][0]...)
		api.Println(sumcheckRounds[i-1][1]...)
		randEval := evaluateFunction(api, sumcheckRounds[i-1][0], sumcheckRounds[i-1][1][0])

		checkSumOverBool(api, randEval, sumcheckRounds[i][0])
	}
}

func firstSumcheckOfARound(api frontend.API, circuit *VerifyMerkleProofCircuit, foldingRandomness []frontend.Variable) {
	//     combinationRandomness := utilities.BigEndian(api, mainSponge.Squeeze(47))
	//     prevPolynEvalAtFoldingRandomness := utilities.QuadraticUnivarPolyFromEvaluations(api, circuit.InitialSumcheckPolyEvals[1], foldingRandomness[len(foldingRandomness)-1])
	//     OODandStirChallengeAnswers := []frontend.Variable{utilities.LittleEndian(api, circuit.OODEvaluations[0])}
	//     for i := range circuit.Answers[0] {
	//         OODandStirChallengeAnswers = append(OODandStirChallengeAnswers, utilities.MultivarPoly(circuit.Answers[0][i], foldingRandomness, api))
	//     }
	//     addedPart := utilities.UnivarPoly(api, OODandStirChallengeAnswers, combinationRandomness)
	//     supposedSum := api.Add(prevPolynEvalAtFoldingRandomness, addedPart)
	//     utilities.CheckSumOverBool(api, supposedSum, circuit.SumcheckPolysAsEvals[0])
}

func checkMainRounds(api frontend.API, circuit *VerifyMerkleProofCircuit, sumcheckRounds [][][]frontend.Variable, sumcheckPolynomials [][]frontend.Variable, finalFoldingRandomness []frontend.Variable, oodAnswersList [][]frontend.Variable, combinationRandomness [][]frontend.Variable) {
	//     //This should be in a for loop
	//     mainSponge.Absorb(circuit.MerkleRoots[0])
	//     mainSponge.Squeeze(47) // OODQuery
	//     mainSponge.Absorb(circuit.OODEvaluations[0])
	//     mainSponge.Squeeze(32) // Stir Queries Seed
	//     mainSponge.Squeeze(32) // Proof of Work queries
	//     mainSponge.Absorb(circuit.Nonce)
	computedFolds := ComputeFolds(api, circuit, sumcheckRounds, finalFoldingRandomness)
	// api.Println(computedFolds)
	for r := 0; r < len(circuit.RoundParametersOODSamples); r++ {

		// api.Println(oodAnswersList[r])
		values := make([]frontend.Variable, len(computedFolds[r])+1)
		values[0] = oodAnswersList[r][0]
		for z := 1; z < len(values); z++ {
			values[z] = computedFolds[r][z-1]
		}
		api.Println(values)
		api.Println(sumcheckRounds)

		api.Println(evaluateFunction(api, sumcheckRounds[r+1][0], sumcheckRounds[r+1][1][0]))
		valuesTimesCombRand := frontend.Variable(0)
		for i := range values {
			product := api.Mul(values[i], combinationRandomness[r][i])
			valuesTimesCombRand = api.Add(valuesTimesCombRand, product)
		}
		claimedSum := api.Add(evaluateFunction(api, sumcheckRounds[r+1][0], sumcheckRounds[r+1][1][0]), valuesTimesCombRand)
		api.Println(claimedSum)

		checkSumOverBool(api, claimedSum, sumcheckPolynomials[r])

		for i := 1; i < len(sumcheckPolynomials); i++ {
			eval := evaluateFunction(api, sumcheckPolynomials[i-1], finalFoldingRandomness[i-1])
			checkSumOverBool(api, eval, sumcheckPolynomials[i])
		}
	}
	// firstSumcheckOfARound(api, circuit, circuit.RoundParametersOODSamples)

	//     mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[0])
	//     foldingRandomness = []frontend.Variable{}
	//     foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))

	//     for i := 1; i < circuit.FoldingParameter; i++ {
	//         randEval := utilities.QuadraticUnivarPolyFromEvaluations(api, circuit.SumcheckPolysAsEvals[i-1], foldingRandomness[len(foldingRandomness)-1])
	//         utilities.CheckSumOverBool(api, randEval, circuit.SumcheckPolysAsEvals[i])
	//         mainSponge.AbsorbQuadraticPolynomial(circuit.SumcheckPolysAsEvals[i])
	//         foldingRandomness = append(foldingRandomness, utilities.BigEndian(api, mainSponge.Squeeze(47)))
	//     }

	//     // Checks in line 512-522 is omitted for now as we need to swap out the ChaCha part. Here is a sketch of what we need to do
	//         // var finalFolds []frontend.Variable
	//         // for i := range circuit.Answers[1] {
	//             // finalFolds = append(finalFolds, utilities.MultivarPoly(circuit.Answers[1][i], foldingRandomness, api))
	//         // }
	//         // finalEvaluations = [Use ChaCha to create random indexes. Use these to get random field elements and evaluate the final polynomial on these random field elements.]
	//         // Check if finalFolds == finalEvaluations

	// api.AssertIsEqual(utilities.LittleEndian(api, circuit.FinalCoeffs), utilities.MultivarPoly(circuit.Answers[1][0], foldingRandomness, api))
}

func ComputeFoldsHelped(api frontend.API, circuit *VerifyMerkleProofCircuit, sumcheckRounds [][][]frontend.Variable, finalFoldingRandomness []frontend.Variable) [][]frontend.Variable {
	result := make([][]frontend.Variable, circuit.ParamNRounds+1)
	for i := range circuit.ParamNRounds {
		evaluations := make([]frontend.Variable, len(circuit.Leaves[i]))
		for j := range circuit.Leaves[i] {
			typeConverters.LittleEndianFromUints(api, circuit.Leaves[i][j][0:8])
			answerList := make([]frontend.Variable, 4)
			for z := range 4 {
				answerList[z] = typeConverters.LittleEndianFromUints(api, circuit.Leaves[i][j][8+z*32:8+32*(z+1)])
			}
			reverseRounds := make([]frontend.Variable, len(sumcheckRounds))
			for z := range 2 {
				reverseRounds[z] = sumcheckRounds[z][1][0]
			}
			evaluations[j] = utilities.MultivarPoly(answerList, reverseRounds, api)
		}
		result[i] = evaluations
	}

	evaluations := make([]frontend.Variable, len(circuit.Leaves[len(circuit.Leaves)-1]))
	for j := range circuit.Leaves[len(circuit.Leaves)-1] {
		typeConverters.LittleEndianFromUints(api, circuit.Leaves[len(circuit.Leaves)-1][j][0:8])
		answerList := make([]frontend.Variable, 4)
		for z := range 4 {
			answerList[z] = typeConverters.LittleEndianFromUints(api, circuit.Leaves[len(circuit.Leaves)-1][j][8+z*32:8+32*(z+1)])
		}
		evaluations[j] = utilities.MultivarPoly(answerList, finalFoldingRandomness, api)
	}
	result[len(result)-1] = evaluations
	return result
}

func ComputeFoldsFull(api frontend.API, circuit *VerifyMerkleProofCircuit) [][]frontend.Variable {
	return nil
}

func ComputeFolds(api frontend.API, circuit *VerifyMerkleProofCircuit, sumcheckRounds [][][]frontend.Variable, finalFoldingRandomness []frontend.Variable) [][]frontend.Variable {
	if circuit.FoldOptimisation {
		return ComputeFoldsHelped(api, circuit, sumcheckRounds, finalFoldingRandomness)
	} else {
		return ComputeFoldsFull(api, circuit)
	}
}

func (circuit *VerifyMerkleProofCircuit) Define(api frontend.API) error {
	arthur, err := gnark_nimue.NewKeccakArthur(api, circuit.IO, circuit.Transcript[:])
	finalFoldingRandomness := make([]frontend.Variable, circuit.FoldingFactor)
	sumcheckPolynomials := make([][]frontend.Variable, circuit.FoldingFactor)
	oodAnswersList := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))
	perRoundCombinationRandomness := make([][]frontend.Variable, len(circuit.RoundParametersOODSamples))

	domainSize := circuit.DomainSize
	if err != nil {
		return err
	}

	rootHash := make([]uints.U8, 32)
	err = arthur.FillNextBytes(rootHash)
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

	combinationRandomnessGenerator := make([]frontend.Variable, 1)
	err = arthur.FillChallengeScalars(combinationRandomnessGenerator)

	if err != nil {
		return err
	}

	api.Println(rootHash)
	api.Println(initialOODAnswers...)
	api.Println(initialOODQueries...)
	api.Println(combinationRandomnessGenerator)

	sumcheckRounds := make([][][]frontend.Variable, circuit.FoldingFactor)
	for i := 0; i < circuit.FoldingFactor; i++ {
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
		api.Println(sumcheckPolynomialEvals)
		api.Println(foldingRandomnessSingle)
		sumcheckRounds[i][0] = sumcheckPolynomialEvals
		sumcheckRounds[i][1] = foldingRandomnessSingle
	}
	roots := make([][]uints.U8, len(circuit.RoundParametersOODSamples))

	for r := 0; r < len(circuit.RoundParametersOODSamples); r++ {
		roots[r] = make([]uints.U8, 32)
		err = arthur.FillNextBytes(roots[r])
		if err != nil {
			return err
		}
		api.Println(roots)

		// err = VerifyMerkleTreeProofs(api, circuit.LeafIndexes[r], circuit.Leaves[r], circuit.LeafSiblingHashes[r], circuit.AuthPaths[r], rootHash)
		// if err != nil {
		// 	return err
		// }

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
			api.Println(oodPoints)
			api.Println(oodAnswers)
			oodAnswersList[r] = oodAnswers
		}

		indexes, err := GetStirChallenges(api, *circuit, arthur, circuit.RoundParametersNumOfQueries[0], domainSize)
		if err != nil {
			return err
		}

		err = IsSubset(api, *circuit, arthur, indexes, circuit.LeafIndexes[0])
		if err != nil {
			return err
		}

		api.Println(circuit.PowBytes)
		if circuit.PowBytes > 0 {
			challenge, nonce, err := PoW(api, arthur)
			if err != nil {
				return err
			}
			api.Println(challenge)
			api.Println(nonce)
		}
		combRandomnessGen := make([]frontend.Variable, 1)
		err = arthur.FillChallengeScalars(combRandomnessGen)
		if err != nil {
			return err
		}
		api.Println(combRandomnessGen...)

		combinationRandomness := ExpandRandomness(api, combRandomnessGen[0], len(circuit.LeafIndexes[r])+circuit.RoundParametersOODSamples[r])
		api.Println(combinationRandomness...)
		perRoundCombinationRandomness[r] = combinationRandomness
		for i := 0; i < circuit.FoldingFactor; i++ {
			sumcheckPoly := make([]frontend.Variable, 3)
			err = arthur.FillNextScalars(sumcheckPoly)
			if err != nil {
				return err
			}
			sumcheckPolynomials[i] = sumcheckPoly
			api.Println(sumcheckPoly...)

			foldingRandomnessSingle := make([]frontend.Variable, 1)
			err = arthur.FillChallengeScalars(foldingRandomnessSingle)
			if err != nil {
				return err
			}
			finalFoldingRandomness[i] = foldingRandomnessSingle[0]
			api.Println(foldingRandomnessSingle...)
		}
	}

	finalCoefficients := make([]frontend.Variable, 1)
	err = arthur.FillNextScalars(finalCoefficients)
	if err != nil {
		return err
	}
	api.Println(finalCoefficients...)

	domainSize /= 2
	finalIndexes, err := GetStirChallenges(api, *circuit, arthur, circuit.FinalQueries, domainSize)
	if err != nil {
		return nil
	}

	err = IsSubset(api, *circuit, arthur, finalIndexes, circuit.LeafIndexes[len(circuit.LeafIndexes)-1])
	if err != nil {
		return err
	}

	// err = VerifyMerkleTreeProofs(api, circuit.LeafIndexes[len(circuit.LeafIndexes)-1], circuit.Leaves[len(circuit.LeafIndexes)-1], circuit.LeafSiblingHashes[len(circuit.LeafIndexes)-1], circuit.AuthPaths[len(circuit.LeafIndexes)-1], roots[0])
	// if err != nil {
	// 	return err
	// }
	if circuit.FinalPowBytes > 0 {
		finalChallenge, finalNonce, err := PoW(api, arthur)
		if err != nil {
			return err
		}
		api.Println(finalChallenge)
		api.Println(finalNonce)
	}

	// for i := 0; i < circuit.FinalSumcheckRounds; i++ {
	// }
	initialSumcheck(api, circuit, initialOODAnswers, combinationRandomnessGenerator[0], sumcheckRounds)
	checkMainRounds(api, circuit, sumcheckRounds, sumcheckPolynomials, finalFoldingRandomness, oodAnswersList, perRoundCombinationRandomness)

	return nil
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

func toLittleEndianBytes(num uint64) []uint8 {
	bytes := make([]uint8, 8)
	for i := 0; i < 8; i++ {
		bytes[i] = uint8(num >> (8 * i) & 0xFF)
	}
	return bytes
}

func verify_circuit(proofs []ProofElement, io string, transcript [560]uints.U8) {
	var totalAuthPath = make([][][][]uints.U8, len(proofs))
	var totalLeaves = make([][][]uints.U8, len(proofs))
	var totalLeafSiblingHashes = make([][][]uints.U8, len(proofs))
	var totalLeafIndexes = make([][]uints.U8, len(proofs))

	var containerTotalAuthPath = make([][][][]uints.U8, len(proofs))
	var containerTotalLeaves = make([][][]uints.U8, len(proofs))
	var containerTotalLeafSiblingHashes = make([][][]uints.U8, len(proofs))
	var containerTotalLeafIndexes = make([][]uints.U8, len(proofs))

	for i := range proofs {

		var numOfLeavesProved = len(proofs[i].A.LeafIndexes)
		var treeHeight = len(proofs[i].A.AuthPathsSuffixes[0])

		totalAuthPath[i] = make([][][]uints.U8, numOfLeavesProved)
		containerTotalAuthPath[i] = make([][][]uints.U8, numOfLeavesProved)
		println(i)
		println(numOfLeavesProved)
		println(treeHeight)
		totalLeaves[i] = make([][]uints.U8, numOfLeavesProved)
		containerTotalLeaves[i] = make([][]uints.U8, numOfLeavesProved)
		totalLeafSiblingHashes[i] = make([][]uints.U8, numOfLeavesProved)
		containerTotalLeafSiblingHashes[i] = make([][]uints.U8, numOfLeavesProved)

		for j := 0; j < numOfLeavesProved; j++ {
			totalAuthPath[i][j] = make([][]uints.U8, treeHeight)
			containerTotalAuthPath[i][j] = make([][]uints.U8, treeHeight)

			for z := 0; z < treeHeight; z++ {
				totalAuthPath[i][j][z] = make([]uints.U8, 32)
				containerTotalAuthPath[i][j][z] = make([]uints.U8, 32)
			}
			totalLeaves[i][j] = make([]uints.U8, 136)
			containerTotalLeaves[i][j] = make([]uints.U8, 136)
			totalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
			containerTotalLeafSiblingHashes[i][j] = make([]uints.U8, 32)
		}

		containerTotalLeafIndexes[i] = make([]uints.U8, numOfLeavesProved)

		var authPathsTemp = make([][]KeccakDigest, numOfLeavesProved)
		var prevPath = proofs[i].A.AuthPathsSuffixes[0]
		authPathsTemp[0] = reverse(prevPath)

		for j := 0; j < len(totalAuthPath[i][0]); j++ {
			totalAuthPath[i][0][j] = uints.NewU8Array(authPathsTemp[0][j].KeccakDigest[:])
		}

		for j := 1; j < numOfLeavesProved; j++ {
			prevPath = prefixDecodePath(prevPath, proofs[i].A.AuthPathsPrefixLengths[j], proofs[i].A.AuthPathsSuffixes[j])
			authPathsTemp[j] = reverse(prevPath)
			for z := 0; z < treeHeight; z++ {
				totalAuthPath[i][j][z] = uints.NewU8Array(authPathsTemp[j][z].KeccakDigest[:])
			}
		}
		totalLeafIndexes[i] = make([]uints.U8, numOfLeavesProved)

		for z := range numOfLeavesProved {
			totalLeafSiblingHashes[i][z] = uints.NewU8Array(proofs[i].A.LeafSiblingHashes[z].KeccakDigest[:])
			totalLeafIndexes[i][z] = uints.NewU8(uint8(proofs[i].A.LeafIndexes[z]))
			big_output := make([]uint8, 136)
			copy(big_output[0:8], toLittleEndianBytes(4))

			for j := range proofs[i].B[z] {
				input := proofs[i].B[z][j]
				output := make([]uint8, 4*8)

				for i, num := range input.Limbs {
					serialized := toLittleEndianBytes(num)
					copy(output[i*8:(i+1)*8], serialized)
				}
				copy(big_output[j*32+8:(j+1)*32+8], output)
			}
			totalLeaves[i][z] = uints.NewU8Array(big_output)
		}
	}

	var circuit = VerifyMerkleProofCircuit{
		IO:                          []byte(io),
		RoundParametersOODSamples:   []int{1},
		RoundParametersNumOfQueries: []int{98, 49},
		ParamNRounds:                1,
		FoldOptimisation:            true,
		CommittmentOODSamples:       1,
		DomainSize:                  32,
		FoldingFactor:               2,
		FinalSumcheckRounds:         0,
		PowBytes:                    2,
		FinalPowBytes:               2,
		FinalQueries:                49,
		StatementPoints:             [][]int{{0, 0, 0, 0}},
		StatementEvaluations:        0,
		Leaves:                      containerTotalLeaves,
		LeafIndexes:                 containerTotalLeafIndexes,
		LeafSiblingHashes:           containerTotalLeafSiblingHashes,
		AuthPaths:                   containerTotalAuthPath,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)

	assignment := VerifyMerkleProofCircuit{
		IO:                          []byte(io),
		Transcript:                  transcript,
		FoldOptimisation:            true,
		CommittmentOODSamples:       1,
		DomainSize:                  32,
		FoldingFactor:               2,
		PowBytes:                    2,
		FinalPowBytes:               2,
		FinalSumcheckRounds:         0,
		RoundParametersOODSamples:   []int{1},
		RoundParametersNumOfQueries: []int{98, 49},
		ParamNRounds:                1,
		FinalQueries:                49,
		StatementPoints:             [][]int{{0, 0, 0, 0}},
		StatementEvaluations:        0,
		Leaves:                      totalLeaves,
		LeafIndexes:                 totalLeafIndexes,
		LeafSiblingHashes:           totalLeafSiblingHashes,
		AuthPaths:                   totalAuthPath,
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness, backend.WithSolverOptions(solver.WithHints(IndexOf)))
	groth16.Verify(proof, vk, publicWitness)
}
