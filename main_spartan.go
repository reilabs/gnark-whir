package main

import (
	"fmt"
	"math/big"
	"tutorial/sumcheck-verifier-circuit/hashmanager"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/iden3/go-iden3-crypto/poseidon"
)

const NUMBER_OF_COEFFS_IN_LINEAR = 2
const NUMBER_OF_COEFFS_IN_QUADRATIC = 3
const NUMBER_OF_COEFFS_IN_CUBIC = 4

var MOD *big.Int
var ONE_HALF_CONSTANT *big.Int

func Init_Spartan() {
	var success bool
	MOD, _ = new(big.Int).SetString("21888242871839275222246405745257275088548364400416034343698204186575808495617", 10)
	ONE_HALF_CONSTANT, success = new(big.Int).SetString("10944121435919637611123202872628637544274182200208017171849102093287904247809", 10)
	if !success {
		fmt.Println("Error: Failed to set big.Int value")
	}
}

type Circuit struct {
	// Alleged computed sum of all the evaluations
	ExpectedSum            frontend.Variable `gnark:"ExpectedSum"`
	ValueAtChallengeVector frontend.Variable `gnark:"ValueAtChallengeVector"`
	// Array of elements representing the values of p0, p1 in each of the rounds
	GPolynomials [][]frontend.Variable `gnark:"GPolynomials"`
}

func (circuit *Circuit) Define(api frontend.API) error {
	var manager = hashmanager.NewHashManager(api)
	g_length := len(circuit.GPolynomials)
	e := circuit.ExpectedSum
	for i := 0; i < g_length; i++ {
		api.AssertIsEqual(len(circuit.GPolynomials[i]), NUMBER_OF_COEFFS_IN_CUBIC)

		// Equivalent constraint to the one below it, doesn't require GPoly[i][0]
		// e = api.Add(api.Mul(ONE_HALF_CONSTANT, api.Add(e, api.Neg(circuit.GPolynomials[i][1]))), api.Mul(circuit.ChallengeVector[i], circuit.GPolynomials[i][1]))
		api.Println(circuit.GPolynomials[i][0], circuit.GPolynomials[i][1])
		r_i := manager.WriteInputAndCollectAndReturnHash(circuit.GPolynomials[i]...)
		api.Println(r_i)
		cumulative := circuit.GPolynomials[i][NUMBER_OF_COEFFS_IN_CUBIC-1]
		for j := NUMBER_OF_COEFFS_IN_CUBIC - 2; j >= 1; j-- {
			cumulative = api.Add(circuit.GPolynomials[i][j], api.Mul(cumulative, r_i))
		}
		e = api.Add(circuit.GPolynomials[i][0], api.Mul(cumulative, r_i))
	}
	api.AssertIsEqual(e, circuit.ValueAtChallengeVector)
	return nil
}

func calculateCubic(e []*big.Int, a_z []*big.Int, b_z []*big.Int, c_z []*big.Int) *big.Int {
	result := big.NewInt(0)
	for i := 0; i < len(e); i++ {
		tmp := new(big.Int).Mul(a_z[i], b_z[i])
		tmp.Sub(tmp, c_z[i])
		tmp.Mul(tmp, e[i])
		result.Add(result, tmp)
	}
	return result
}

func replace_r_in_f(f []*big.Int, r *big.Int) []*big.Int {
	n := len(f) / 2
	for i := 0; i < n; i++ {
		diff := new(big.Int).Sub(f[n+i], f[i]) // diff = f[n+i] - f[i]
		scaled := new(big.Int).Mul(r, diff)    // scaled = r * diff
		f[i].Add(f[i], scaled)                 // f[i] += scaled
	}
	return f[:n]
}

func main_spartan() {
	Init_Spartan()

	// START R1CS case
	// Sum_x e(x) * (a(x) * b(x) - c(x))
	var number_of_variables = 2

	// initialize coefficients
	var coeffs_univariate_polynomials = make([][]frontend.Variable, number_of_variables)
	for i := 0; i < number_of_variables; i++ {
		coeffs_univariate_polynomials[i] = make([]frontend.Variable, NUMBER_OF_COEFFS_IN_CUBIC)
	}
	var circuit = Circuit{
		GPolynomials: coeffs_univariate_polynomials,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	pk, vk, _ := groth16.Setup(ccs)
	// proof for some random values of e, Az, Bz, Cz
	// still to validate for real A,B,C and its witness vector

	// Commented out since VerifyR1CS() is not defined in the provided code
	// VerifyR1CS()

	// Initialize arrays with *big.Int
	var e = []*big.Int{
		big.NewInt(1),
		big.NewInt(4),
		big.NewInt(3),
		big.NewInt(6),
		big.NewInt(3),
		big.NewInt(5),
		big.NewInt(0),
		big.NewInt(0),
	}

	var a_z = []*big.Int{
		big.NewInt(3),
		big.NewInt(9),
		big.NewInt(30),
		big.NewInt(25),
		big.NewInt(5),
		big.NewInt(25),
		big.NewInt(0),
		big.NewInt(0),
	}

	var b_z = []*big.Int{
		big.NewInt(3),
		big.NewInt(3),
		big.NewInt(1),
		big.NewInt(1),
		big.NewInt(5),
		big.NewInt(1),
		big.NewInt(0),
		big.NewInt(0),
	}

	var c_z = []*big.Int{
		big.NewInt(9),
		big.NewInt(27),
		big.NewInt(30),
		big.NewInt(25),
		big.NewInt(25),
		big.NewInt(25),
		big.NewInt(0),
		big.NewInt(0),
	}

	var initial_expected_sum = calculateCubic(e, a_z, b_z, c_z)
	var expected_sum = new(big.Int).Set(initial_expected_sum)
	var challenge_vector []frontend.Variable

	fmt.Println("Initial Expected Sum:", expected_sum)

	for i := 0; i < number_of_variables; i++ {
		p_0 := big.NewInt(0)
		p_tmp := big.NewInt(0)
		p_3 := big.NewInt(0)
		offset := len(e) / 2
		for j := 0; j < len(e)/2; j++ {
			// p_0 += e[j] * (a_z[j]*b_z[j] - c_z[j])
			temp1 := new(big.Int).Mul(a_z[j], b_z[j]) // a_z[j]*a_z[j]
			temp1.Sub(temp1, c_z[j])                  // temp1 = temp1 - c_z[j]
			temp1.Mul(temp1, e[j])                    // temp1 = e[j] * (a_z[j]*b_z[j] - c_z[j])
			p_0.Add(p_0, temp1)
			p_0.Mod(temp1, MOD)

			// p_tmp += (2*e[j] - e[j+offset]) * ((2*a_z[j]-a_z[j+offset])*(2*b_z[j]-b_z[j+offset]) - (2*c_z[j] - c_z[j+offset]))
			temp2 := new(big.Int).Mul(big.NewInt(2), e[j]) // 2*e[j]
			temp2.Sub(temp2, e[j+offset])                  // temp2 = (2*e[j] - e[j+offset])

			temp3 := new(big.Int).Mul(big.NewInt(2), a_z[j]) // 2*a_z[j]
			temp3.Sub(temp3, a_z[j+offset])                  // temp3 = (2*a_z[j] - a_z[j+offset])

			temp4 := new(big.Int).Mul(big.NewInt(2), b_z[j]) // 2*b_z[j]
			temp4.Sub(temp4, b_z[j+offset])                  // temp4 = (2*b_z[j] - b_z[j+offset])

			temp5 := new(big.Int).Mul(temp3, temp4) // temp5 = temp3 * temp4

			temp6 := new(big.Int).Mul(big.NewInt(2), c_z[j]) // 2*c_z[j]
			temp6.Sub(temp6, c_z[j+offset])                  // temp6 = (2*c_z[j] - c_z[j+offset])

			temp7 := new(big.Int).Sub(temp5, temp6) // temp7 = temp5 - temp6

			temp8 := new(big.Int).Mul(temp2, temp7) // temp8 = temp2 * temp7

			p_tmp.Add(p_tmp, temp8)
			p_tmp.Mod(p_tmp, MOD)

			// p_3 += (e[j+offset] - e[j]) * (a_z[j+offset] - a_z[j]) * (b_z[j+offset] - b_z[j])
			temp9 := new(big.Int).Sub(e[j+offset], e[j])      // temp9 = e[j+offset] - e[j]
			temp10 := new(big.Int).Sub(a_z[j+offset], a_z[j]) // temp10 = a_z[j+offset] - a_z[j]
			temp11 := new(big.Int).Sub(b_z[j+offset], b_z[j]) // temp11 = b_z[j+offset] - b_z[j]

			temp12 := new(big.Int).Mul(temp9, temp10)
			temp12.Mul(temp12, temp11)

			p_3.Add(p_3, temp12)
			p_3.Mod(p_3, MOD)
		}

		// p_2 := (expected_sum + p_tmp - p_0 - p_0 - p_0) / 2
		temp13 := new(big.Int).Add(expected_sum, p_tmp)
		temp13.Sub(temp13, p_0)
		temp13.Sub(temp13, p_0)
		temp13.Sub(temp13, p_0)

		p_2 := new(big.Int).Div(temp13, big.NewInt(2))
		p_2.Mod(p_2, MOD)
		// p_1 := expected_sum - p_0 - p_0 - p_3 - p_2
		p_1 := new(big.Int).Sub(expected_sum, p_0)
		p_1.Sub(p_1, p_0)
		p_1.Sub(p_1, p_3)
		p_1.Sub(p_1, p_2)
		p_1.Mod(p_1, MOD)

		coeffs_univariate_polynomials[i] = []frontend.Variable{p_0, p_1, p_2, p_3}
		hash_value, _ := poseidon.Hash([]*big.Int{p_0, p_1, p_2, p_3})
		// Generate a random *big.Int less than 11
		r := hash_value
		fmt.Println("r_", i, " = ", r)
		challenge_vector = append(challenge_vector, r)

		e = replace_r_in_f(e, r)
		a_z = replace_r_in_f(a_z, r)
		b_z = replace_r_in_f(b_z, r)
		c_z = replace_r_in_f(c_z, r)

		// expected_sum = p_0 + r*(p_1 + r*(p_2 + r*p_3))
		temp14 := new(big.Int).Mul(r, p_3) // r * p_3
		temp14.Add(temp14, p_2)            // p_2 + r * p_3
		temp14.Mul(temp14, r)              // r * (p_2 + r * p_3)
		temp14.Add(temp14, p_1)            // p_1 + r * (p_2 + r * p_3)
		temp14.Mul(temp14, r)              // r * (p_1 + r * (p_2 + r * p_3))
		expected_sum = new(big.Int).Add(p_0, temp14)
		expected_sum.Mod(expected_sum, MOD)
	}

	assignment := Circuit{
		ExpectedSum:            initial_expected_sum,
		ValueAtChallengeVector: expected_sum,
		GPolynomials:           coeffs_univariate_polynomials,
	}
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, pk, witness)
	groth16.Verify(proof, vk, publicWitness)
	//END R1CS case
}
