package main

import (
	"fmt"
	"math/big"
)

const target = 50000

func main() {
	f := new(big.Int)
	c := new(big.Int)
	one := new(big.Int)

	f.SetInt64(1)
	c.SetInt64(1)
	one.SetInt64(1)

	for i := 0; i < target; i++ {
		f.Mul(f, c)
		c.Add(c, one)
	}

	fmt.Printf("%s", f.String())
}
