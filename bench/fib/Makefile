TIME = /usr/bin/time -f "%E real, %U user, %S sys"

all: run

run: build
	@printf -- "------ fibonacci (lladd, llsub) \n"
	@printf   "fib-zig: " && $(TIME) ./fib-zig | md5sum
	@printf   "  debug: " && $(TIME) ./fib-zig-debug | md5sum

	@printf "\nfib-c:   " && $(TIME) ./fib-c| md5sum

	@printf "\nfib-go:  " && $(TIME) ./fib-go  | md5sum

	@printf "\nfib-py:  " && $(TIME) ./fib-py  | md5sum

	@printf "\nfib-rs:  " && $(TIME) ./fib-rs  | md5sum

build: fib-zig fib-zig-debug fib-c fib-go fib-py fib-rs

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

clean:
	rm -f fib-zig fib-zig-debug fib-c fib-go fib-rs fib-rs-debug

.PHONY: clean
