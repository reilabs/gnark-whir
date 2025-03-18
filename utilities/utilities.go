package utilities

import (
	"github.com/consensys/gnark/frontend"
)

func MultivarPoly(coefs []frontend.Variable, vars []frontend.Variable, api frontend.API) frontend.Variable {
	if len(vars) == 0 {
		return coefs[0]
	}

	// if len(vars) == 1 {
	// 	return api.Add(api.Mul(vars[0], coefs[1]), coefs[0])
	// }

	// if len(vars) == 2 {
	// 	b0 := api.Add(coefs[0], api.Mul(coefs[1], vars[1]))
	// 	b1 := api.Add(coefs[2], api.Mul(coefs[3], vars[1]))
	// 	return api.Add(b0, api.Mul(b1, vars[0]))
	// }

	// if len(vars) == 3 {
	// 	x0 := vars[0]
	// 	x1 := vars[1]
	// 	x2 := vars[2]
	// 	b00 := api.Add(coefs[0], api.Mul(coefs[1], x2))
	// 	b01 := api.Add(coefs[2], api.Mul(coefs[3], x2))
	// 	b10 := api.Add(coefs[4], api.Mul(coefs[5], x2))
	// 	b11 := api.Add(coefs[6], api.Mul(coefs[7], x2))
	// 	b0 := api.Add(b00, api.Mul(b01, x1))
	// 	b1 := api.Add(b10, api.Mul(b11, x1))
	// 	return api.Add(b0, api.Mul(b1, x0))
	// }

	// if len(vars) == 4 {
	// 	x0 := vars[0]
	// 	x1 := vars[1]
	// 	x2 := vars[2]
	// 	x3 := vars[3]
	// 	b000 := api.Add(coefs[0], api.Mul(coefs[1], x3))
	// 	b001 := api.Add(coefs[2], api.Mul(coefs[3], x3))
	// 	b010 := api.Add(coefs[4], api.Mul(coefs[5], x3))
	// 	b011 := api.Add(coefs[6], api.Mul(coefs[7], x3))
	// 	b100 := api.Add(coefs[8], api.Mul(coefs[9], x3))
	// 	b101 := api.Add(coefs[10], api.Mul(coefs[11], x3))
	// 	b110 := api.Add(coefs[12], api.Mul(coefs[13], x3))
	// 	b111 := api.Add(coefs[14], api.Mul(coefs[15], x3))

	// 	b00 := api.Add(b000, api.Mul(b001, x2))
	// 	b01 := api.Add(b010, api.Mul(b011, x2))
	// 	b10 := api.Add(b100, api.Mul(b101, x2))
	// 	b11 := api.Add(b110, api.Mul(b111, x2))
	// 	b0 := api.Add(b00, api.Mul(b01, x1))
	// 	b1 := api.Add(b10, api.Mul(b11, x1))
	// 	return api.Add(b0, api.Mul(b1, x0))
	// }

	deg_zero := MultivarPoly(coefs[:len(coefs)/2], vars[:len(vars)-1], api)
	deg_one := api.Mul(vars[len(vars)-1], MultivarPoly(coefs[len(coefs)/2:], vars[:len(vars)-1], api))
	return api.Add(deg_zero, deg_one)
}

func UnivarPoly(api frontend.API, coefficients []frontend.Variable, points []frontend.Variable) []frontend.Variable {
	results := make([]frontend.Variable, len(points))
	for j := range points {
		ans := frontend.Variable(0)
		for i := range coefficients {
			ans = api.Add(api.Mul(ans, points[j]), coefficients[len(coefficients)-1-i])
		}
		results[j] = ans
	}
	return results
}
