package utilities

import (
	"github.com/consensys/gnark/frontend"
	"math/big"
)

func BigEndian(api frontend.API, varArr []frontend.Variable) frontend.Variable {
    frontendVar := frontend.Variable(0)
    for i := range varArr {
		frontendVar = api.Add(api.Mul(256, frontendVar), varArr[i])
	}
    return frontendVar
}

func LittleEndian(api frontend.API, varArr []frontend.Variable) frontend.Variable {
	frontendVar := frontend.Variable(0)
    for i := range varArr {
		frontendVar = api.Add(api.Mul(256, frontendVar), varArr[len(varArr) - 1 - i])
    }
    return frontendVar
}

func LittleEndianArr(api frontend.API, arrVarArr [][]frontend.Variable) []frontend.Variable {
	frontendArr := make([]frontend.Variable, len(arrVarArr))
	
	for j := range arrVarArr {
		frontendVar := frontend.Variable(0)
		for i := range arrVarArr[j] {
			frontendVar = api.Add(api.Mul(256, frontendVar), arrVarArr[j][len(arrVarArr[j]) - 1 - i])
		}
		frontendArr[j] = frontendVar
	}
    return frontendArr
}

func ByteArrToVarArr(uint8Arr []uint8) []frontend.Variable {
    frontendArr := make([]frontend.Variable, len(uint8Arr))
    for i := range frontendArr {
        frontendArr[i] = frontend.Variable(uint8Arr[i])
    }
    return frontendArr
}

func MultivarPoly (coefs []frontend.Variable, vars []frontend.Variable, api frontend.API) frontend.Variable {
	if (len(vars) == 0) { return coefs[0] }
	deg_zero := MultivarPoly(coefs[:len(coefs)/2], vars[:len(vars)-1], api)
	deg_one := api.Mul(vars[len(vars)-1], MultivarPoly(coefs[len(coefs)/2:], vars[:len(vars)-1], api))
	return api.Add(deg_zero, deg_one)
}

func UnivarPoly (api frontend.API, coefficients []frontend.Variable, point frontend.Variable) frontend.Variable {
    ans := frontend.Variable(0)
    for i := range coefficients {
        ans = api.Add(api.Mul(ans, point), coefficients[len(coefficients)-1-i])
    }
    return ans;
}

func QuadraticUnivarPolyFromEvaluations (api frontend.API, evaluationsAsBytes [][]frontend.Variable, point frontend.Variable) (ans frontend.Variable) {
    evaluations := LittleEndianArr(api, evaluationsAsBytes)
    inv2 := api.Inverse(2)
    b0 := evaluations[0]
    b1 := api.Mul(api.Add(api.Neg(evaluations[2]), api.Mul(4, evaluations[1]), api.Mul(-3, evaluations[0])), inv2)
    b2 := api.Mul(api.Add(evaluations[2],api.Mul(-2, evaluations[1]), evaluations[0]), inv2)
    return api.Add(api.Mul(point, point, b2), api.Mul(point, b1), b0)
}

func CheckSumOverBool (api frontend.API, value frontend.Variable, polyEvals [][]frontend.Variable) {
    sumOverBools := api.Add(
        LittleEndian(api, polyEvals[0]), 
        LittleEndian(api, polyEvals[1]),
    )
    api.AssertIsEqual(value, sumOverBools)
}

func NewBigIntFromString(s string) *big.Int {
    bigInt, _ := new(big.Int).SetString(s, 10)
    return bigInt
}

func StrToVar (str string) frontend.Variable {
    return frontend.Variable(NewBigIntFromString(str))
}

func StrArrToVarArr(strArr []string) []frontend.Variable {
    var ans []frontend.Variable
    for _, v := range strArr {
        ans = append(ans, StrToVar(v))
    }
    return ans;
}

func Str2DArrToVar2DArr(str2DArr [][]string) [][]frontend.Variable {
    var ans [][]frontend.Variable
    for i := range str2DArr {
        ans = append(ans, StrArrToVarArr(str2DArr[i]))
    }
    return ans;
}

func Byte2DArrToVar2DArr(byte2DArr [][]uint8) [][]frontend.Variable {
    var ans [][]frontend.Variable
    for i := range byte2DArr {
        ans = append(ans, ByteArrToVarArr(byte2DArr[i]))
    }
    return ans;
}

func Str3DArrToVar3DArr(str3DArr [][][]string) [][][]frontend.Variable {
    var ans [][][]frontend.Variable
    for i := range str3DArr {
        ans = append(ans, Str2DArrToVar2DArr(str3DArr[i]))
    }
    return ans;
}

func Byte3DArrToVar3DArr(byte3DArr [][][]uint8) [][][]frontend.Variable {
    var ans [][][]frontend.Variable
    for i := range byte3DArr {
        ans = append(ans, Byte2DArrToVar2DArr(byte3DArr[i]))
    }
    return ans;
}
