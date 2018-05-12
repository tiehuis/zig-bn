TIME = /usr/bin/time -f "%E real, %U user, %S sys"

all: run

run: build
	@printf -- "------ facdiv (llmul, lldiv1, divN) \n"
	@printf   "facdiv-zig: " && $(TIME) ./facdiv-zig | md5sum

	@printf "\nfacdiv-c:   " && $(TIME) ./facdiv-c   | md5sum

	@printf "\nfacdiv-go:  " && $(TIME) ./facdiv-go  | md5sum

	@printf "\nfacdiv-py:  " && $(TIME) ./facdiv-py  | md5sum

	@printf "\nfacdiv-rs:  " && $(TIME) ./facdiv-rs  | md5sum

build: facdiv-zig facdiv-c facdiv-go facdiv-py facdiv-rs

facdiv-zig: facdiv.zig
	zig build-exe facdiv.zig --library c --output facdiv-zig --release-fast

facdiv-c: facdiv.c
	gcc -O2 facdiv.c -lgmp -o facdiv-c

facdiv-go: facdiv.go
	go build -o facdiv-go facdiv.go

facdiv-rs: crate-facdiv-rs/src/main.rs
	cd crate-facdiv-rs && cargo build --release && cp target/release/facdiv-rs ..

clean:
	rm -f facdiv-zig facdiv-c facdiv-go facdiv-rs

.PHONY: clean
