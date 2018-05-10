package main

import (
	"fmt"
	"math/big"
)

const target = 200000

func main() {
	f0 := new(big.Int)
	f1 := new(big.Int)

	f0.SetInt64(1)
	f1.SetInt64(1)

	for i := 0; i < target; i++ {
		f1.Add(f1, f0)
		f0.Sub(f1, f0)
	}

	fmt.Printf("%x", f1)
}
