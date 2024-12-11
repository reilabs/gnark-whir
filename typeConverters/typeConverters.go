package typeConverters

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/uints"
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
		frontendVar = api.Add(api.Mul(256, frontendVar), varArr[len(varArr)-1-i])
	}
	return frontendVar
}

func LittleEndianFromUints(api frontend.API, varArr []uints.U8) frontend.Variable {
	frontendVar := frontend.Variable(0)
	for i := range varArr {
		frontendVar = api.Add(api.Mul(256, frontendVar), varArr[len(varArr)-1-i].Val)
	}
	return frontendVar
}

func LittleEndianArr(api frontend.API, arrVarArr [][]frontend.Variable) []frontend.Variable {
	frontendArr := make([]frontend.Variable, len(arrVarArr))

	for j := range arrVarArr {
		frontendVar := frontend.Variable(0)
		for i := range arrVarArr[j] {
			frontendVar = api.Add(api.Mul(256, frontendVar), arrVarArr[j][len(arrVarArr[j])-1-i])
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
