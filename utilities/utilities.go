package utilities

import (
	"github.com/consensys/gnark/frontend"
)

func MultivarPoly(coefs []frontend.Variable, vars []frontend.Variable, api frontend.API) frontend.Variable {
	if len(vars) == 0 {
		return coefs[0]
	}
	deg_zero := MultivarPoly(coefs[:len(coefs)/2], vars[:len(vars)-1], api)
	deg_one := api.Mul(vars[len(vars)-1], MultivarPoly(coefs[len(coefs)/2:], vars[:len(vars)-1], api))
	return api.Add(deg_zero, deg_one)
}
