package main

import (
	"math/big"
)

const target = 100000

func main() {
	f0 := new(big.Int)
	f1 := new(big.Int)

	f0.SetInt64(1)
	f1.SetInt64(1)

	for i := 0; i < target; i++ {
		f1.Add(f1, f0)
		f0.Sub(f1, f0)
	}

	// print(f1.String())
}
