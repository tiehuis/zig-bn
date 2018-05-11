TIME = /usr/bin/time -f "%E real, %U user, %S sys"

all: run

run: build
	@printf -- "------ factorial (llmul, lladd) \n"
	@printf   "fac-zig: " && $(TIME) ./fac-zig | md5sum

	@printf "\nfac-c:   " && $(TIME) ./fac-c   | md5sum

	@printf "\nfac-go:  " && $(TIME) ./fac-go  | md5sum

	@printf "\nfac-py:  " && $(TIME) ./fac-py  | md5sum

	@printf "\nfac-rs:  " && $(TIME) ./fac-rs  | md5sum

build: fac-zig fac-c fac-go fac-py fac-rs

fac-zig: fac.zig
	zig build-exe fac.zig --library c --output fac-zig --release-fast

fac-c: fac.c
	gcc -O2 fac.c -lgmp -o fac-c

fac-go: fac.go
	go build -o fac-go fac.go

fac-rs: crate-fac-rs/src/main.rs
	cd crate-fac-rs && cargo build --release && cp target/release/fac-rs ..

clean:
	rm -f fac-zig fac-c fac-go fac-rs

.PHONY: clean
