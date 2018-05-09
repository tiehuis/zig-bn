TIME = /usr/bin/time -f "%E real, %U user, %S sys"

all: run-fac run-fib

build: build-fac build-fib

run-fac: build-fac
	@printf -- "------ factorial (llmul, lladd) \n"
	@printf   "fac-zig: " && $(TIME) ./fac-zig | md5sum

	@printf "\nfac-c:   " && $(TIME) ./fac-c   | md5sum

	@printf "\nfac-go:  " && $(TIME) ./fac-go  | md5sum

	@printf "\nfac-py:  " && $(TIME) ./fac-py  | md5sum

	@printf "\nfac-rs:  " && $(TIME) ./fac-rs | md5sum

build-fac: fac-zig fac-c fac-go fac-py fac-rs

fac-zig: fac.zig
	zig build-exe fac.zig --library c --output fac-zig --release-fast

fac-c: fac.c
	gcc -O2 fac.c -lgmp -o fac-c

fac-go: fac.go
	go build -o fac-go fac.go

fac-rs: crate-fac-rs/src/main.rs
	cd crate-fac-rs && cargo build --release && cp target/release/fac-rs ..


run-fib: build-fib
	@printf -- "------ fibonacci (lladd, llsub) \n"
	@printf   "fib-zig: " && $(TIME) ./fib-zig
	@printf   "  debug: " && $(TIME) ./fib-zig-debug  | md5sum

	@printf "\nfib-c:   " && $(TIME) ./fib-c   | md5sum

	@printf "\nfib-go:  " && $(TIME) ./fib-go  | md5sum

	@printf "\nfib-py:  " && $(TIME) ./fib-py  | md5sum

	@printf "\nfib-rs:  " && $(TIME) ./fib-rs

build-fib: fib-zig fib-zig-debug fib-c fib-go fib-py fib-rs

fib-zig: fib.zig
	zig build-exe fib.zig --library c --output fib-zig --release-fast

fib-zig-debug: fib.zig
	zig build-exe fib.zig --library c --output fib-zig-debug

fib-c: fib.c
	gcc -O2 fib.c -lgmp -o fib-c

fib-go: fib.go
	go build -o fib-go fib.go

fib-rs: crate-fib-rs/src/main.rs
	cd crate-fib-rs && cargo build --release && cp target/release/fib-rs ..

# ignored for now; too slow.
fib-rs-debug: crate-fib-rs/src/main.rs
	cd crate-fib-rs && cargo build && cp target/debug/fib-rs ../fib-rs-debug


system: cpu version

cpu:
	@lscpu
	@printf "\n"

version:
	@printf "zig:  " && zig version
	@printf "gcc:  " && gcc --version | head -n1
	@printf "go:   " && go version
	@printf "py:   " && python3 --version
	@printf "rust: " && rustc --version

clean:
	rm -f fib-zig fib-zig-debug fib-c fib-go fib-rs fib-rs-debug \
		fac-zig fac-c fac-go fac-rs

.PHONY: clean version
